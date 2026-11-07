-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_dropWhile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:13.211229+00:00
-- url     : https://prove2.me/submissions/f8ba55ca-9717-4342-a385-20227f14ac9f

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
theorem _root_.solution (a b q : ℕ) :
    (tripleInput a b q).dropWhile id = false :: pairInput b q := by
  induction a with
  | zero => simp [tripleInput,unary]
  | succ a ih => simpa [tripleInput,unary_succ] using ih
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
