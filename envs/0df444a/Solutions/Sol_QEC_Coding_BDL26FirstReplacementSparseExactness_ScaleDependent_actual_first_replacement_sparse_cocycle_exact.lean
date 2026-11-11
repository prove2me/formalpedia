-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.actual_first_replacement_sparse_cocycle_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:45:24.441209+00:00
-- url     : https://prove2.me/submissions/93ae1278-00fb-453b-be1a-51c3be5ac673

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exists_zero_slice
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_zero_slice_readout
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exact_of_zero_slice
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_exists_zero_slice
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_zero_slice_readout
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_exact_of_zero_slice

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (k : Nat)
    (large : k+2 ≤ S.half)
    (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤k) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  change w ∈ LinearMap.range (tannerCoboundary0 (rxReplacementPresentation Seed S))
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at closed
  obtain ⟨j,hj⟩ := exists_zero_slice S k large w small
  exact exact_of_zero_slice S k large w closed j (zero_slice_readout S k large j w hj)
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
