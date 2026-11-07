-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount.rowCount_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:45.277018+00:00
-- url     : https://prove2.me/submissions/c0990196-08ef-4d16-9734-92346f90e8ea

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SparseEmitterRowCount_rowCount_unary_append

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
theorem _root_.solution (a b c d:ℕ) (w:List Bool):
 rowCount 0 (stream [a,b,c,d]++w)=rowCount 0 w+1:=by
 simp [stream,List.append_assoc,rowCount_unary_append,rowCount,advance]
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterRowCount
