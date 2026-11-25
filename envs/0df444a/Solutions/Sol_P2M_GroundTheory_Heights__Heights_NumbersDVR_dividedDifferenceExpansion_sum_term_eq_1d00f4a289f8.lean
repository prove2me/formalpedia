-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:20.939373+00:00
-- url     : https://prove2.me/submissions/f4c47dd7-8168-4366-aaa3-b979cdcb4f83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_term_eq_b68ba4cef9fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
namespace GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
theorem _root_.solution {r : ℕ} (μ : Fin r →₀ ℕ) :
    ∑ l : Fin r, (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      ∏ j, X (Sum.inl j) ^ μ j - ∏ j, X (Sum.inr j) ^ μ j := by
  simp_rw [term_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => stair μ i - stair μ (i + 1)) r,
    Finset.sum_range_sub', stair_zero, stair_top]
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
