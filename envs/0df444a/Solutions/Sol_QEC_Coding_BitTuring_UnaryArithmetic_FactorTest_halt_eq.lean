-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.halt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:20.23299+00:00
-- url     : https://prove2.me/submissions/f7f022d6-11f0-4602-bce6-c6014cbdab1f

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
theorem _root_.solution (d : List Bool) : machine.halt d = finalHalt d := by
  rfl
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
