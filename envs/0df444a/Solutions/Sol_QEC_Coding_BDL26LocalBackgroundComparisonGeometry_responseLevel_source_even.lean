-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonGeometry.responseLevel_source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:42:45.935598+00:00
-- url     : https://prove2.me/submissions/62087d32-57a5-49e0-87d2-9631f84321fb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_budgetDepth_source_even


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalBackgroundComparisonResponse BDL26LocalBackgroundComparisonDepth
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26LocalBackgroundComparisonGeometry
theorem _root_.solution (t R : ℝ) :
    responseLevel t R=2*(4*ballBudget t R+2) ∧ 0 < responseLevel t R := by
  have h := budgetDepth_source_even (ballBudget t R)
  unfold responseLevel
  omega
end QEC.Coding.BDL26LocalBackgroundComparisonGeometry
