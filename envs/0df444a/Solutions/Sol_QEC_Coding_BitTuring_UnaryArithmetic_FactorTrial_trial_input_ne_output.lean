-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.trial_input_ne_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:55.805406+00:00
-- url     : https://prove2.me/submissions/473d3df3-85d6-4311-8eac-d8fe520c560f

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
theorem _root_.solution : trialMachine.input ≠ trialMachine.output := by
  simp [trialMachine,Composition.machine]
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
