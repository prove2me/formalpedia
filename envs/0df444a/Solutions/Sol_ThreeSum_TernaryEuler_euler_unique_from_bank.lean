-- Prove2me | solution 1 for ThreeSum.TernaryEuler.euler_unique_from_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:17.101798+00:00
-- url     : https://prove2.me/submissions/619e51d3-b0ed-45fb-8b2e-fd4e8a6e5242

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_rank_lt
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N h T : ℕ} (hcut : h ≤ T)
    (F G : TritWord N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ bank N T, F R = G R) : F = G := by
  funext R
  have hall : ∀ k, ∀ R : TritWord N, rank R = k → F R = G R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hR
      by_cases hlow : rank R ≤ T
      · exact hbank R (mem_bank.mpr hlow)
      · have hsum : (∑ i : Fin N, (R i).val * F (predecessor R i)) =
            ∑ i : Fin N, (R i).val * G (predecessor R i) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hz : (R i).val = 0
          · simp [hz]
          · have hr := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz)
            rw [ih (rank (predecessor R i)) (by omega) (predecessor R i) rfl]
        rw [hF R, hG R] at hsum
        have hn : ((rank R : ℤ) - (h : ℤ)) ≠ 0 := by
          have : h < rank R := by omega
          omega
        exact mul_left_cancel₀ hn hsum
  exact hall (rank R) R rfl
end ThreeSum.TernaryEuler
