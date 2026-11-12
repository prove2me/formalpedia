-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_Q_coordinate_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:16:12.945548+00:00
-- url     : https://prove2.me/submissions/e8055516-f5cb-4e36-a542-c91c2569607e

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
theorem _root_.solution (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) p.val =
      @Vertex.q (state S 2).presentation (q2 S) := by
  change BDL26RXDecoderAdapter.vertexEquiv (state S 2).presentation
    ((A S).topCenter p.val) = @Vertex.q (state S 2).presentation (q2 S)
  rw [((A S).topCenter_q_iff (q2 S) p.val).mp p.property]
  rfl
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
