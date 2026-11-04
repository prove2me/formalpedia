-- Prove2me | solution 1 for ThreeSum.TernaryReconstruction.recover_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:18.082273+00:00
-- url     : https://prove2.me/submissions/b2e006d5-fc1c-4875-a8f3-b8e987403ff0

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_rank_lt
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryReconstruction
theorem _root_.solution {N h T : ℕ} (hcut : h ≤ T) (seed F : TritWord N → ℤ)
    (hbank : ∀ R ∈ bank N T, seed R = F R)
    (hEuler : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (fuel : ℕ) (R : TritWord N) (hbound : rank R ≤ T + fuel) :
    recover seed h T fuel R = F R := by
  induction fuel generalizing R with
  | zero =>
      exact hbank R (mem_bank.mpr (by simpa using hbound))
  | succ k ih =>
      simp only [recover]
      by_cases hlow : rank R ≤ T
      · simp [hlow, hbank R (mem_bank.mpr hlow)]
      · simp only [hlow, ↓reduceIte]
        have hsum : (∑ i : Fin N, if (R i).val = 0 then 0 else
              (R i).val * recover seed h T k (predecessor R i)) =
            ∑ i : Fin N, (R i).val * F (predecessor R i) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hz : (R i).val = 0
          · simp [hz]
          · have hr := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz)
            simp only [hz, ↓reduceIte]
            rw [ih (predecessor R i) (by omega)]
        rw [hsum, hEuler]
        have hn : ((rank R : ℤ) - (h : ℤ)) ≠ 0 := by
          have : h < rank R := by omega
          omega
        exact Int.mul_ediv_cancel_left _ hn
end ThreeSum.TernaryReconstruction
