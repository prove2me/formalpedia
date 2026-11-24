-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:35.034762+00:00
-- url     : https://prove2.me/submissions/11cffd1c-972f-4e04-bd88-3920751a13c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SheetSumMeasurable
theorem _root_.solution : SheetSumMeasurable.Statement := by
  intro n d J A g φ _ _ hA hg _
  refine ⟨SheetSumMeasurable.measurable_sheetSum hA (fun a b => a * b)
    (continuous_fst.mul continuous_snd).measurable hg φ,
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      (continuous_fst.mul continuous_snd).abs.measurable hg φ⟩
end SheetSumMeasurable
end GroundTheory.Heights₂.Heights
