-- Prove2me | solution 1 for burau_cfList_eq_cfPair_v2
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T23:26:38.290798+00:00
-- url     : https://prove2.me/submissions/f2d7fcb6-0181-46d6-89a8-6c225fa9bd1e

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_cf_pair

set_option autoImplicit false

open Matrix

/-- The quotient list of the matrix descent agrees with the integer-level recursion `cfPair`. -/
theorem solution (M : BurauNC.M2) :
    BurauNC.cfList M = BurauNC.cfPair (M 0 0) (M 0 1) := by
  have main : ∀ k : ℕ, ∀ M : BurauNC.M2,
      (M 0 0).natAbs ≤ k → BurauNC.cfList M = BurauNC.cfPair (M 0 0) (M 0 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro M hk
      by_cases h : M 0 0 = 0
      · rw [BurauNC.cfList_eq_nil M h, h, BurauNC.cfPair_zero]
      · have hlt : (((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 0).natAbs
            < (M 0 0).natAbs := BurauNC.euclid_decrease M h
        have hlt' : (((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 0).natAbs < k := by omega
        have hrow0 : ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 0 = M 0 1 % M 0 0 := by
          rw [BurauNC.Tm, BurauNC.Sm]
          simp [Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def] <;> ring
        have hrow1 : ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 1 = -(M 0 0) := by
          rw [BurauNC.Tm, BurauNC.Sm]
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
        rw [BurauNC.cfList_cons M h, BurauNC.cfPair_cons (M 0 0) (M 0 1) h,
          ih (((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) 0 0).natAbs hlt'
            ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) le_rfl, hrow0, hrow1]
  exact main (M 0 0).natAbs M le_rfl
