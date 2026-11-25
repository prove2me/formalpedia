-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:02.319299+00:00
-- url     : https://prove2.me/submissions/f2aa801d-1c0f-469e-a935-d3ac2a08e823

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ofMetrics_fs_h_bd4ac42ff7dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_base_9953fcac61b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_det_0c73e0eee300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_base_47f3f062edc6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_det_46d28ee0f0c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_line0_ea32279785ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_otherLine_3e6f27535fdb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) (HermLine.ofMetrics (fun k => fsMetric (ExY k)) c) (exPull 0 c) := by
  refine ⟨rfl, fun z => ?_⟩
  have e1 : I1.pullDeg (diagonalBlockIndex 0) c .base = c .base := pullDeg_segreBlockEmbedding 0 c .base
  have e2 : I1.pullDeg (diagonalBlockIndex 0) c .det = c .det := pullDeg_segreBlockEmbedding 0 c .det
  have e3 : I1.pullDeg (diagonalBlockIndex 0) c .line0 = c .line := pullDeg_segreBlockEmbedding 0 c .line
  have e4 : I1.pullDeg (diagonalBlockIndex 0) c .line1 = 0 := pullDeg_otherLine 0 c
  rw [exPull, ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, sumW_base, sumW_det, sumW_line0, sumW_line1,
    sumY_base, sumY_det, sumY_line, e1, e2, e3, e4]
  simp [T.yyEmb]
end GroundTheory.Heights₂.Heights.Inter
