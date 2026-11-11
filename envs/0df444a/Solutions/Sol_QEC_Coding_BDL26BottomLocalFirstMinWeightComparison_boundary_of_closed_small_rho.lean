-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_small_rho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:48:58.417426+00:00
-- url     : https://prove2.me/submissions/475b55d1-3365-4397-9709-faf21f97b5fb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_actual_first_replacement_sparse_cocycle_exact
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_closed
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_boundary_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half)
    (w : Error S) (hw : tannerCoboundary1 (P2 S) w = 0)
    (small : HammingWeight (rho S w) ≤ 14) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply (rho_boundary_iff S w hw).2
  exact BDL26FirstReplacementSparseExactness.actual_first_replacement_sparse_cocycle_exact
    S large (rho S w) (rho_closed S w hw) small
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
