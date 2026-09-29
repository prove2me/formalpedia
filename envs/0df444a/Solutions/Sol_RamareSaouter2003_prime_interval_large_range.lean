-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:42:52.202115+00:00
-- url     : https://prove2.me/submissions/e4a722ac-ff10-4eae-997c-9ec496576a80
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RamareSaouter2003_weighted_interval_mass_gt_one
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem solution (x : ℝ) (hx : 10 ^ (20 : ℕ) ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  classical
  by_contra hno
  have hzero :
      Finset.sum (Finset.range (Nat.floor x + 1))
        (fun p => if p.Prime ∧ x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x
          then Real.log (p : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hband : p.Prime ∧
        x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x
    · exact (hno ⟨p, hband.1, hband.2.1, hband.2.2⟩).elim
    · rw [if_neg hband]
  have hmass := RamareSaouter2003.weighted_interval_mass_gt_one x hx
  rw [hzero] at hmass
  norm_num at hmass
