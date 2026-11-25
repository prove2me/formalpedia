-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:46.979567+00:00
-- url     : https://prove2.me/submissions/1388f0aa-ae8f-4b3c-9d90-b2082f518a6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_antisym_psumAt_mul_adaccf6e47a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_eq_zero_of_swap_01c116fa164d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
