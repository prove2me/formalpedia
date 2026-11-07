-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:58.386193+00:00
-- url     : https://prove2.me/submissions/efc6cbee-5466-41ca-bbc7-2ca9fde823b5

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution : Function.Injective stream := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons b ys =>
      have hl:=congrArg List.length h
      simp [stream,unary_length] at hl
  | cons a xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have hl:=congrArg List.length h
      simp [stream,unary_length] at hl
    | cons b ys =>
      have he:=@UnaryOutputEquality.prefixInput_injective (a,stream xs) (b,stream ys) h
      exact congrArg₂ List.cons (congrArg Prod.fst he) (ih (congrArg Prod.snd he))
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
