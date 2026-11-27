-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regLine_inhabited_e7961a3755ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:33.599658+00:00
-- url     : https://prove2.me/submissions/af81f056-30dd-4b92-bf63-18b06caf3bbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Inter
namespace regLine
theorem _root_.solution :
    IsSmoothHerm (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1) ∧
      (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).a = 0 ∧
      ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 3))), eval z (map (Int.castRingHom ℂ) (Xc 3 0)) ≠ 0 →
        logNorm (fsLine 3) (Xc 3 0) z ≤
          Real.log ((regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).h z) :=
  ⟨isSmoothHerm_regLine (isSmoothHerm_fsLine 3) one_pos, rfl,
    fun _ hz h0 => logNorm_le_log_regLine_h zero_le_one hz.1 h0⟩
end regLine
end GroundTheory.Heights₂.Heights.Inter
