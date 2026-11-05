-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory.runSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:23:26.32294+00:00
-- url     : https://prove2.me/submissions/cae0dfed-847d-4195-8329-70eb12609b49

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
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
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory
theorem _root_.solution {C : Config} [Fact C.p.Prime] {D : Data C} {depth : ℕ} {μ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : SpanGuard C D lim μ) :
    Meets lim LightStoredSpan.program 6 (depth+1) [C.catalog,C.catalogRows,C.J,C.row] μ
      (LightSpanCatalogTest.time C.J C.catalogRows) (fun r ν => r=D.flag ∧ ν=μ) := by
  exact LightStoredSpan.program_admissible_meets μ D.catalog
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) H.represents G.spaceWord H.catalogSpace
    (by have := G.rowBefore; have := G.BC; have := G.CO; have := G.outScratch; have := G.scratchSpace; omega)
    H.controls H.pword H.bounded H.read
    (by intro i hi; rw [G.coeffRead i (by omega),H.digits i hi]) (by have := G.depth; omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalSeedScoreFactory
