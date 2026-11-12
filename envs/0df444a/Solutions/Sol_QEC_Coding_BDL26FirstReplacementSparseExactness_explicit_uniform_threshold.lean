-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.explicit_uniform_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:13:40.475787+00:00
-- url     : https://prove2.me/submissions/d675dc1f-1f14-4ca6-bf03-10d14127004f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_actual_first_replacement_sparse_cocycle_exact

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution :
    ∃ H : Nat, ∀ S : OddScale, H≤S.half →
      ∀ w : Word Bit (BDL26DecodingGraph.state S 1).presentation.Q,
        tannerCoboundary1 (BDL26DecodingGraph.state S 1).presentation w=0 →
        HammingWeight w≤14 →
        w ∈ LinearMap.range (tannerCoboundary0 (BDL26DecodingGraph.state S 1).presentation) := by
  exact ⟨16,actual_first_replacement_sparse_cocycle_exact⟩
end QEC.Coding.BDL26FirstReplacementSparseExactness
