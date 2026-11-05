-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory.SpanGuard.run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:30:12.798738+00:00
-- url     : https://prove2.me/submissions/e08d320b-88a8-487c-8a89-994e5e4e2d71

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_controls
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory
namespace SpanGuard
theorem _root_.solution {C : Config} [Fact C.p.Prime] {D : Data C} {lim : Limits}
    {depth newSpan : ℕ} {μ : ℕ→ℤ} (G : SpanGuard C D lim depth newSpan μ) :
    Meets lim LightStoredSpan.program 1 depth [C.catalog,C.catalogRows,C.row,newSpan,C.J,C.p]
      μ (LightSpanCatalogStep.time C.J C.p C.catalogRows) (fun _ ν=>SpanDone C D newSpan μ ν) :=by
  exact LightStoredSpan.program_step_meets μ D.catalog
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) G.represents G.rowsPos
    G.spaceWord G.source G.row G.output G.word G.controls G.bounded G.read G.rowRead G.depth
end SpanGuard
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory
