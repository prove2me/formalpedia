-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:05.434506+00:00
-- url     : https://prove2.me/submissions/92132f19-6579-43cb-bec0-c23119ed124f

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (xs:List ℕ) : (raw xs).length≤(stream xs).length := by
  simp only [raw,List.length_dropLast];omega
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
