-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetImageAreaSet_areaJacobian_comp_of_norm_5fbe9dbf23fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:02.784478+00:00
-- url     : https://prove2.me/submissions/ce2d4ef3-2312-4c5f-8e6d-cfa8eedaac94

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
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]
end GroundTheory.Heights₂.Heights.SheetImageAreaSet
