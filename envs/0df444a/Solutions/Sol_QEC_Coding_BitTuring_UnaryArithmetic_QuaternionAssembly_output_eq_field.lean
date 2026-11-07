-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.output_eq_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:30.735205+00:00
-- url     : https://prove2.me/submissions/4e07b3ae-449d-45a7-a216-ee444e00bb2c

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
open Turing StateTransition FieldProjection
open Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
theorem _root_.solution (q:ℕ) (hq:0<q) (s y d c b a:ZMod q) :
    output s.val y.val d.val c.val b.val a.val q=raw
      [((y*d+a)*s).val,((-(y*b)+c)*s).val,((-c+-(y*b))*s).val,((-(y*d)+a)*s).val] := by
  let : NeZero q:=⟨hq.ne'⟩
  have hn (z:ZMod q) : ModularNegation.output z.val q=(-z).val := by
    rw [ModularNegation.output_eq_neg _ _ hq (ZMod.val_lt _),ZMod.natCast_zmod_val]
  simp only [output,←ZMod.val_mul,hn,←ZMod.val_add]
end QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
