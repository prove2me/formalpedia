-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_proof_c2014608166d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:58.919637+00:00
-- url     : https://prove2.me/submissions/db7a3203-8edb-497b-ae7b-fd3cdb419c0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_sum_term_eq_1d00f4a289f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_eq_sum_5b30b6969504
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_rename_divDiff_31bd75b02a7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isHomogeneous_divDiff_55f04f213f1e


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
theorem _root_.solution : dividedDifferenceExpansion.Statement := by
  intro r m G hG
  refine ⟨?_, ?_⟩
  · rw [rename_eq_sum, rename_eq_sum, ← Finset.sum_sub_distrib]
    calc ∑ μ ∈ G.support, (C (G.coeff μ) * ∏ j, X (Sum.inl j) ^ μ j -
            C (G.coeff μ) * ∏ j, X (Sum.inr j) ^ μ j)
        = ∑ μ ∈ G.support, ∑ l : Fin r, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_congr rfl fun μ _ => by rw [← Finset.mul_sum, sum_term_eq, mul_sub]
      _ = ∑ l : Fin r, ∑ μ ∈ G.support, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => by
          rw [rename_divDiff, Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  · intro l
    rcases m with _ | d
    · have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G = 0 := by
        unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
        refine Finset.sum_eq_zero fun μ hμ => ?_
        have h := hG (mem_support_iff.mp hμ)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
        have hl : μ l = 0 := by
          have h' : ∑ j, μ j = 0 := by simpa using h
          exact (Finset.sum_eq_zero_iff.mp h') l (Finset.mem_univ l)
        simp [hl]
      rw [h0, map_zero]
      exact isHomogeneous_zero _ _ _
    · simpa using (BundleExamples.isHomogeneous_divDiff l hG).rename_isHomogeneous
        (f := finSumFinEquiv.symm)
end GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion
