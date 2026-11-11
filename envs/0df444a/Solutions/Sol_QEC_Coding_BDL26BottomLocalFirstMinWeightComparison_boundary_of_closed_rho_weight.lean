-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.boundary_of_closed_rho_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:48:33.567081+00:00
-- url     : https://prove2.me/submissions/620dc455-af6e-48c2-b384-a9fdb1cb413f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_actual_first_replacement_sparse_cocycle_exact
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_closed
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_actual_first_replacement_sparse_cocycle_exact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half) (w : Error S)
    (closed : tannerCoboundary1 (P2 S) w=0)
    (small : HammingWeight (rho S w) ≤ k) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply (rho_boundary_iff S w closed).2
  exact BDL26FirstReplacementSparseExactness.ScaleDependent.actual_first_replacement_sparse_cocycle_exact
    S k large (rho S w) (rho_closed S w closed) small
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
