-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.actual_first_replacement_sparse_cocycle_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:48:30.966645+00:00
-- url     : https://prove2.me/submissions/1e4535d7-533b-41f3-baa1-3e867fd255dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exists_zero_slice
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_zero_slice_readout
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_exact_of_zero_slice

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (S : OddScale)
    (large : 16 ≤ S.half) (w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q)
    (closed : tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0)
    (small : HammingWeight w≤14) :
    w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  change w ∈ LinearMap.range (tannerCoboundary0 (rxReplacementPresentation Seed S))
  change tannerCoboundary1 (rxReplacementPresentation Seed S) w=0 at closed
  obtain ⟨k,hk⟩ := exists_zero_slice S large w small
  exact exact_of_zero_slice S large w closed k (zero_slice_readout S large k w hk)
end QEC.Coding.BDL26FirstReplacementSparseExactness
