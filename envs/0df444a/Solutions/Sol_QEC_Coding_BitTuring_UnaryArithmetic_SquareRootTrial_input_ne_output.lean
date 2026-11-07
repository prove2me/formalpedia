-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial.input_ne_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:02.265234+00:00
-- url     : https://prove2.me/submissions/b8d18f83-1cef-48c6-81f5-4d5cf92c4540

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial
theorem _root_.solution : machine.input≠machine.output := by
  simp [machine,Composition.machine]
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRootTrial
