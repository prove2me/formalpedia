-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_append_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:48.638167+00:00
-- url     : https://prove2.me/submissions/9a7de7b6-957b-4a2f-aae0-de8be6e27b00

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (xs:List ℕ) (a:ℕ) :
    raw (xs++[a])=stream xs++unary a := by
  induction xs with
  | nil=>simp [raw,stream]
  | cons b xs ih=>
    change (unary b++false::stream (xs++[a])).dropLast=_
    have hn:stream (xs++[a])≠[] := by
      intro h
      have hl:=congrArg List.length h
      simp only [stream_length,List.length_nil,List.length_append,List.length_singleton] at hl
      omega
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
      List.dropLast_cons_of_ne_nil hn]
    -- separator persists because the remainder contains at least its final delimiter.
    change unary b++false::raw (xs++[a])=_
    rw [ih];simp only [stream,List.cons_append,List.append_assoc]
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
