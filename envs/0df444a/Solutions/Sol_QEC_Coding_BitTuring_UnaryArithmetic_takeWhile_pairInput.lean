-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.takeWhile_pairInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:54.033685+00:00
-- url     : https://prove2.me/submissions/4caebe1b-8554-4be6-b500-36d38f87cace

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution (a b : ℕ) : (pairInput a b).takeWhile id = unary a := by
  induction a with
  | zero => simp [pairInput]
  | succ a ih => simpa [pairInput, unary_succ] using congrArg (List.cons true) ih
end QEC.Coding.BitTuring.UnaryArithmetic
