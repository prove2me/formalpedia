-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial.input_ne_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:47.615051+00:00
-- url     : https://prove2.me/submissions/f178b947-87ee-4d51-9cc6-c93f032d665c

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryProductTrial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
theorem _root_.solution : machine.input≠machine.output := by
  simp [machine,Composition.machine]
end QEC.Coding.BitTuring.UnaryArithmetic.ProductTrial
