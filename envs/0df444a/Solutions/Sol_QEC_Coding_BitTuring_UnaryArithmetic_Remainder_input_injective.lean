-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.Remainder.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:27.508842+00:00
-- url     : https://prove2.me/submissions/0c887f9e-eaba-4489-9f3d-3d728feac22e

import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_pairInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.Remainder
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.Remainder
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have hh := @pairInput_injective (x.1,x.2.val) (y.1,y.2.val) h
  have ha : x.1=y.1 := congrArg (fun z:ℕ×ℕ => z.1) hh
  have hq : x.2.val=y.2.val := congrArg (fun z:ℕ×ℕ => z.2) hh
  exact Prod.ext ha (Subtype.ext hq)
end QEC.Coding.BitTuring.UnaryArithmetic.Remainder
