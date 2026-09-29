-- Prove2me | solution 1 for Supermodularity.Games.equilibrium_iff_fixed_point
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T00:51:20.879296+00:00
-- url     : https://prove2.me/submissions/4fac4091-ce7b-4289-b722-4038f00e0691

import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

open Supermodularity.Games

/-- The equivalence fails for a game without players: with no players every joint strategy is
vacuously a best joint response to itself, but with an empty feasible set nothing is an
equilibrium. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ),
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x') := by
  intro H
  have h := @H PEmpty _ _ (fun _ => 0) ∅ (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
  have hB : (fun i => PEmpty.elim i : ∀ i : PEmpty, Fin ((fun _ => 0) i) → ℝ) ∈
      BestJointResponse (∅ : Set (∀ i : PEmpty, Fin ((fun _ => 0) i) → ℝ))
        (fun i => PEmpty.elim i) (fun i => PEmpty.elim i) :=
    fun i => PEmpty.elim i
  exact (h.mpr hB).1
