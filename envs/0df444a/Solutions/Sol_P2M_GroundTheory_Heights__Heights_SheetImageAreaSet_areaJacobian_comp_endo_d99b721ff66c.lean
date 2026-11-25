-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_endo_d99b721ff66c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:55.009414+00:00
-- url     : https://prove2.me/submissions/7339070f-f5a9-4757-9f37-dac327303a58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_eq_normDet_42419aa0db84

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
open Module
noncomputable section
open GroundTheory.Heights₂.Heights.SheetImageAreaSet
namespace GroundTheory.Heights₂.Heights.SheetImageAreaSet
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]
end GroundTheory.Heights₂.Heights.SheetImageAreaSet
