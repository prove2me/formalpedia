-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:26.547767+00:00
-- url     : https://prove2.me/submissions/6a8d092e-dc51-4993-9779-f307291dfa67

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (a b q:ℕ) : raw [a,b,q]=FactorTest.tripleInput a b q := by
  have h:=raw_append_last [a,b] q
  simpa [stream,FactorTest.tripleInput,pairInput,List.append_assoc] using h
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
