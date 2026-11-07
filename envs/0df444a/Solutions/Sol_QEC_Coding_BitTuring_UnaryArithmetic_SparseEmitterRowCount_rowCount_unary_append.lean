-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount.rowCount_unary_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:28.767074+00:00
-- url     : https://prove2.me/submissions/15c6b218-f470-4b33-846a-a588b17db888

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
theorem _root_.solution (k:Fin 4) (n:ℕ) (w:List Bool):rowCount k (unary n++w)=rowCount k w:=by
 induction n with
 | zero=>simp [unary]
 | succ n ih=>simp [unary_succ,rowCount,ih]
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
