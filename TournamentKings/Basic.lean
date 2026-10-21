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
end
end TournamentKings
