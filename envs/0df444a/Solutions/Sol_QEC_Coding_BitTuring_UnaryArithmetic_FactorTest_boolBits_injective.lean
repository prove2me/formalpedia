-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.boolBits_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:32.95871+00:00
-- url     : https://prove2.me/submissions/80ed10f7-116f-42db-a625-fce73dfc9854

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
theorem _root_.solution : Function.Injective boolBits := by
  intro x y h
  exact (List.cons.inj h).1
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
