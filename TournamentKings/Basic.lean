import Mathlib

namespace TournamentKings

/-!
# Kings in Tournament Graphs

Vertices represent teams.
An edge from v to u means that v defeated u in a match.

Main goal: prove that every vertex of maximum outdegree is a king.
-/

structure Tournament (V : Type*) where
  Beats : V → V → Prop
  no_self : ∀ v, ¬Beats v v
  total : ∀ u v, u ≠ v → Beats u v ∨ Beats v u
  asymmetric : ∀ u v, Beats u v → ¬Beats v u

variable {V : Type*}

noncomputable section

/-- The finite set of opponents defeated by v-/
def defeatedOpponents [Fintype V]
    (T : Tournament V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => T.Beats v u)

/-! ## Outdegree

The outdegree of a vertex is it's number of wins.
We count the elements of its defeated-opponents set.
-/

/-- The number of opponents defeated by v-/
def outdegree [Fintype V] (T : Tournament V) (v : V) : ℕ :=
  (defeatedOpponents T v).card

/-! ## Kings
A king can reach every other vertex in one or two steps.
In sports terms, it either defeated a team or defeated
another team that defeated that team.
-/

/-- A vertex that reaches every other vertex in one or two steps-/
def isKing (T : Tournament V) (v : V) : Prop :=
  ∀ u, u ≠ v → T.Beats v u ∨ ∃ w, T.Beats v w ∧ T.Beats w u

/-! ## Maximum Outdegree

A vertex has maximum outdegree if everyother vertex has
at most as many wins. Several vertices can tie for the maximum
-/

/-- No vertex has more wins than v. -/
def HasMaximumOutdegree [Fintype V]
    (T : Tournament V) (v : V) : Prop :=
  ∀ u, outdegree T u ≤ outdegree T v

/-! ## Membership in the Defeated-Opponents Set

This lemma lets us translate between finite-set membership
and the statement that one team defeated another.
-/

/-- u belongs to v's defeated-opponents set exactly when v beats u-/
theorem mem_defeatedOpponents [Fintype V]
    (T : Tournament V) (v u : V) :
    u ∈ defeatedOpponents T v ↔ T.Beats v u := by
  classical
  simp [defeatedOpponents]

/-! ## Existence of a Maximum-Outdegree Vertex

There are finitely many vertices and at least one vertex,
so some vertex has at least as many wins as every other vertex
-/

/-- Every finite, nonempty tournament has a maximum-outdegree vertex-/
theorem exists_maximum_outdegree [Fintype V] [Nonempty V]
    (T : Tournament V) :
    ∃ v, HasMaximumOutdegree T v := by
  classical
  -- Choose a vertex maximizing outdegree among all vertices.
  obtain ⟨v, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V)
      (outdegree T) Finset.univ_nonempty
  use v
  intro u
  exact hmax u (Finset.mem_univ u)

/-! ## Unreachable Vertices

If v cannot reach a disctinct vertex u in one or two steps,
then u beats v and every opponent defeated by v.
-/

/-- An unreachable vertex beats v and all of v's defeated opponenets. -/
theorem unreachable_beats_all
    (T : Tournament V) (v u : V)
    (hne : u ≠ v)
    (hno_direct : ¬T.Beats v u)
    (hno_two : ¬ ∃ w, T.Beats v w ∧ T.Beats w u) :
    T.Beats u v ∧ ∀ w, T.Beats v w → T.Beats u w := by
  constructor
  · -- One team must win; v does not beat u, so u beats v
    rcases T.total u v hne with huv | hvu
    · exact huv
    · exact False.elim (hno_direct hvu)
  · intro w hvw
    -- If w = u, then v beats u, conttradicting hno_direct
    have hwu : w ≠ u := by
      intro heq
      subst w
      exact hno_direct hvw
    rcases T.total w u hwu with hwu_win | huw
    · -- v beating w and w beating u would give a two-step route.
      exact False.elim (hno_two ⟨w, hvw, hwu_win⟩)
    · exact huw

/-! ## Comparing Outdegrees

If u beats v and every opponent v beats, then u's defeated-opponents
set contains all of v's defeated opponents plus at least one more: v.
-/

/-- Beating v and all of v's defeated opponents gives u more wins. -/
theorem outdegree_lt_of_beats_all [Fintype V]
  (T : Tournament V) (v u : V)
  (huv : T.beats u v)
  (hall : T.beats u v)
  (hall : ∀ w, T.Beats v w → T.Beats u w) :
  outdegree T v < outdegree T u := by
  --Every opponent v beats also belongs to u's set.
  have hsubset : defeatedOpponents T v ⊆ defeatedOpponents T u := by
    intro w hwv
    have hvw : T.beats v w := (mem_defeatedOponnents t v w).mp hw
    exact (mem_defeatedOpponents T u w).mpr (hall w hvw)

  --The reverse inclusion fails: u beats v, but v cannot beat itself.
  have hnot_reverse : ¬ (defeatedOpponents T u ⊆ defeatedOpponents T v) := by
    intro hreverse
    have hmem_u : v ∈ defeatedOpponents T u :=
      (mem_defeatedOpponents T u v).mpr huv
    have hmem_v : v ∈ defeatedOpponents T v := hreverse hmem_u
    exact T.no_self v ((mem_defeatedOpponents T v v).mp hmem_v)

  --A proper subset of a finite set has fewer elements.
  have hstrict : defeatedOpponents T v ⊂ defeatedOpponents T u :=
    lt_of_le_not_le hsubset hnot_reverse
  exact Finset.card_lt_card hstrict


end
end TournamentKings
