-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceMultGeneral_proof_5274b99dbf03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:25.926092+00:00
-- url     : https://prove2.me/submissions/2e0ed1af-5398-4c4e-a68c-f633bdc2d106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_component_3855e668464c

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
open MvPolynomial Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace SliceMultGeneral
theorem _root_.solution (hC : CMGeneralPoint.Statement) (hT : TransverseSliceGeneral.Statement)
    (hL : LengthTransverseSlice.Statement) : SliceMultGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  have hdW := ringKrullDim_component hu hW hdim
  obtain ⟨f₁, hf₁W, hf₁⟩ := hC n _ W hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hT n d W hWp hdW
  refine ⟨f₁ * f₂, fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W, fun q hq hqf => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hqf
  obtain ⟨hone, hcm⟩ := hf₁ q hq hqf.1
  obtain ⟨hO, hD⟩ := hf₂ q hq hqf.2
  refine ⟨_, hO, hD, fun L hL' => ?_⟩
  have hsl : sliceIdeal J L q ⊔ Ideal.span {linForm u} = sliceIdeal (J ⊔ Ideal.span {linForm u}) L q := by
    simp only [sliceIdeal, sup_right_comm]
  rw [hsl]
  exact hL n d _ W q L hW hdW hq hone hcm hL'
end SliceMultGeneral
end GroundTheory.Heights₂.Heights
