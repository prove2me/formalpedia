-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.mid_Z_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:04:26.305203+00:00
-- url     : https://prove2.me/submissions/936035cb-d373-4f21-87f7-70e77b5129d4

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
theorem _root_.solution (S : OddScale) :
    parent S 2 (zVertex S 2 (r2 S)) = some (zVertex S 1 (baseRetainedZ S)) := by
  change rzParent (state S 1).presentation
    (state S 1).admissible.toTannerSquareAdmissible S
    (Vertex.z (r2 S)) = some (Vertex.z (baseRetainedZ S))
  rfl
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
