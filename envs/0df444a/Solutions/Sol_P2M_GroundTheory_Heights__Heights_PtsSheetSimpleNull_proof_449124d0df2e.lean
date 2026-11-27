-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_proof_449124d0df2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:29.509321+00:00
-- url     : https://prove2.me/submissions/aa480614-bb7f-4324-834b-f9860bf678de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetSimpleNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_simple_of_count_5ad89185d088
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)
namespace GroundTheory.Heights₂.Heights
namespace PtsSheetSimpleNull
theorem _root_.solution (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)
end PtsSheetSimpleNull
end GroundTheory.Heights₂.Heights
