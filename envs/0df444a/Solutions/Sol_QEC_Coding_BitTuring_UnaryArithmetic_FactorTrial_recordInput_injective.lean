-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial.recordInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:44.691198+00:00
-- url     : https://prove2.me/submissions/11a1ac62-5318-440e-9df7-a27a54fda4cc

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
theorem _root_.solution : Function.Injective recordInput := by
  intro x y h
  exact Subtype.ext (FactorTest.tripleInput_injective h)
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTrial
