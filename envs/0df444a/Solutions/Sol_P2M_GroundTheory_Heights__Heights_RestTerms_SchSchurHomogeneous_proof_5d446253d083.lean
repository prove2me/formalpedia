-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurHomogeneous_proof_5d446253d083
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:36.090515+00:00
-- url     : https://prove2.me/submissions/63c492ee-8352-4966-b5bf-ec838e27450b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchSchurHomogeneous
theorem _root_.solution : SchSchurHomogeneous.Statement := by
  intro σ _ _ r lam
  unfold schur
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun π _ => ?_
  rw [Units.smul_def]
  have hmem : (∏ i, (Matrix.of fun i j : Fin r =>
      completeSymmetric σ ((lam i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ))) (π i) i) ∈
      homogeneousSubmodule σ ℚ (∑ i, lam i) := by
    rw [mem_homogeneousSubmodule]
    by_cases h : ∀ i, 0 ≤ (lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)
    · have hdeg : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat = ∑ i, lam i := by
        have h1 : ((∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h i)
        have h2 : ∑ i, ((lam (π i) : ℤ) - ((π i : ℕ) : ℤ) + ((i : ℕ) : ℤ)) = ∑ i, (lam i : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Equiv.sum_comp π (fun i => (lam i : ℤ)), Equiv.sum_comp π (fun i => ((i : ℕ) : ℤ))]
          ring
        exact_mod_cast h1.trans h2
      rw [← hdeg]
      refine IsHomogeneous.prod _ _ _ fun i _ => ?_
      simp only [Matrix.of_apply, completeSymmetric, if_pos (h i)]
      exact hsymm_isHomogeneous σ _
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [completeSymmetric, not_le.mpr hi])]
      exact isHomogeneous_zero _ _ _
  exact zsmul_mem hmem _
end SchSchurHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
