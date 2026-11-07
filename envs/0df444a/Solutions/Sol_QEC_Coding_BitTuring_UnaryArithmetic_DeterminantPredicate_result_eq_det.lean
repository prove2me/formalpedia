-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.result_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:36.356458+00:00
-- url     : https://prove2.me/submissions/5deaa978-9ad3-454c-a25e-5c95a93a68e3

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection QuaternionAssembly
namespace QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
theorem _root_.solution (q:ℕ) (hq:0<q) (a b c d:ZMod q) :
    result a.val b.val c.val d.val q=(!![a,b;c,d]).det.val :=by
  let : NeZero q:=⟨hq.ne'⟩
  have hn (z:ZMod q):ModularNegation.output z.val q=(-z).val :=by
    rw [ModularNegation.output_eq_neg _ _ hq (ZMod.val_lt _),ZMod.natCast_zmod_val]
  simp only [result,←ZMod.val_mul,hn,←ZMod.val_add]
  rw [Matrix.det_fin_two]
  congr 1
  simp [sub_eq_add_neg,add_comm]
end QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
