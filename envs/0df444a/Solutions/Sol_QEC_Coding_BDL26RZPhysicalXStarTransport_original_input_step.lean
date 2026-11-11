-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:14:41.416116+00:00
-- url     : https://prove2.me/submissions/13877499-a040-4734-893b-b3aef891894c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_original_input_eq
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
open BDL26HistorySyndromeSensitivity
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (S : OddScale) (n : Nat) (s : TopInput S n) (k : StepIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s k.castSucc=
      (BDL26CanonicalHistoryMarks.outputAt S n s k).coarse := by
  rw [original_input_eq,BDL26CanonicalHistoryMarks.outputAt,original_input_eq]
  exact actualInputs_step S n s k
end QEC.Coding.BDL26RZPhysicalXStarTransport
