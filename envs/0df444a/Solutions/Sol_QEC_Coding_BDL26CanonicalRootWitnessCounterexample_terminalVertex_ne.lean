-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.terminalVertex_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:03:16.677276+00:00
-- url     : https://prove2.me/submissions/882ab51c-6043-478f-a64a-43bd81fd8f2d

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
    (z : (state S 2).presentation.Z) (hqz : (state S 2).presentation.qz q z = true) :
    terminalVertex S q z hqz 0 ≠ terminalVertex S q z hqz 1 := by
  intro he
  have hc := (rxQVertexEquiv S 4 (2 : StepIndex 4) (by decide) q).injective he
  have hb := congrArg Prod.fst hc
  exact (by decide : (0 : Fin 2) ≠ 1) hb
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
