-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_takeWhile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:13:35.917289+00:00
-- url     : https://prove2.me/submissions/05db8330-eb7f-46a2-8a07-f7463fbb858f

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
theorem _root_.solution (a b q : ℕ) :
    (tripleInput a b q).takeWhile id = unary a := by
  induction a with
  | zero => simp [tripleInput,unary]
  | succ a ih => simpa [tripleInput,unary_succ] using congrArg (List.cons true) ih
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
