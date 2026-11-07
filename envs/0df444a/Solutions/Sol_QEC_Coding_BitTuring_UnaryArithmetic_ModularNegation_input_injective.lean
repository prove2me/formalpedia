-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:11:22.893839+00:00
-- url     : https://prove2.me/submissions/0eabd5bb-38ba-42e6-a3e5-b66af2f5999b

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_pairInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have he:=@pairInput_injective (x.val.1,x.val.2.val) (y.val.1,y.val.2.val) h
  have ha:x.val.1=y.val.1:=congrArg (fun z:ℕ×ℕ=>z.1) he
  have hq:x.val.2.val=y.val.2.val:=congrArg (fun z:ℕ×ℕ=>z.2) he
  exact Subtype.ext (Prod.ext ha (Subtype.ext hq))
end QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
