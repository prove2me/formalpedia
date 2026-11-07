-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.dropWhile_pairInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:04:24.831212+00:00
-- url     : https://prove2.me/submissions/fe0bb000-bf0c-48d6-a537-5126878d882b

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution (a b : ℕ) : (pairInput a b).dropWhile id = false :: unary b := by
  induction a with
  | zero => simp [pairInput]
  | succ a ih => simpa [pairInput, unary_succ] using ih
end QEC.Coding.BitTuring.UnaryArithmetic
