-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.retained_top_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:14:15.060505+00:00
-- url     : https://prove2.me/submissions/3aaa909e-f3c3-40cc-a508-de407acd9d68

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
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (b : Fin 2) :
    parent S 3 (zVertex S 3 ((A S).induced.zPairEquiv (r2 S,b)).val) =
      some (zVertex S 2 (r2 S)) := by
  change rxParent (state S 2).presentation S
    (Vertex.z (Sum.inr (r2 S,b))) = some (Vertex.z (r2 S))
  rfl
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
