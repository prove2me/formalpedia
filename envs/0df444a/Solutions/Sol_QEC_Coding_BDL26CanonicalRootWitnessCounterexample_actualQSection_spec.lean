-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actualQSection_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:00:23.433531+00:00
-- url     : https://prove2.me/submissions/2ee43834-d8da-4857-b769-aecd0ceb6ddc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (q : (state S 2).presentation.Q)
    (t : LocalQSyndrome S q)
    (ht : t ∈ LinearMap.range ((A S).contract.rx_local_complexes.cqDelta1 q)) :
    (A S).contract.rx_local_complexes.cqDelta1 q (actualQSection S q t ht) = t ∧
      HammingWeight ((A S).contract.support_decomposition.cqFlow q
        (actualQSection S q t ht)) ≤ HammingWeight t :=
  Classical.choose_spec ((A S).contract.local_boundary_weight_budgets.cq q t ht)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
