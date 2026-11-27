-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_proof_b383ce6a628c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:26.69445+00:00
-- url     : https://prove2.me/submissions/d41aed6d-22f5-4c6f-9fb5-a881edb99ad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_secM_eq_span_49c37a72a880
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomial_bound_07979692c060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SpanningAtDominantWeight
theorem _root_.solution : SpanningAtDominantWeight.Statement := by
  intro ι _ _ n Ω _ y b m x' hx' τ
  have hτ : (fun _ : Unit ↦ τ) = τ • fun _ : Unit ↦ 1 := by
    funext
    simp
  refine ⟨?_, SpanningAtDominantWeight.secM_eq_span y (τ • b), fun A Q hA z hz μ hμ ↦ SpanningAtDominantWeight.monomial_bound hA hz τ μ hμ,
    fun A hAa hA μ hμ ↦ SpanningAtDominantWeight.isSmallH_monomial y A b hAa hA τ μ hμ⟩
  rw [SpanningAtDominantWeight.secM_eq_span, SpanningAtDominantWeight.secM_eq_span, hτ, SpanningAtDominantWeight.monomialValues_nsmul,
    SpanningAtDominantWeight.monomialValues_one_block, SpanningAtDominantWeight.monomialValues_nsmul, ← Submodule.span_pow, ← Submodule.span_pow, hx']
end SpanningAtDominantWeight
end GroundTheory.Heights₂.Heights
