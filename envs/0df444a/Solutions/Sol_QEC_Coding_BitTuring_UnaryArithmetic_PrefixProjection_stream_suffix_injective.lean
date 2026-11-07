-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.stream_suffix_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:28.197356+00:00
-- url     : https://prove2.me/submissions/142f902b-7841-471f-bae2-93fb4df8db90

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
theorem _root_.solution (xs ys:List ℕ) (s t:List Bool) (hl:xs.length=ys.length)
    (h:stream xs++s=stream ys++t):xs=ys ∧ s=t :=by
  induction xs generalizing ys s t with
  | nil=>
    have hy:ys=[]:=by simpa only [List.length_nil,List.length_eq_zero_iff] using hl.symm
    subst ys
    exact ⟨rfl,by simpa only [stream,List.nil_append] using h⟩
  | cons a xs ih=>
    cases ys with
    | nil=>simp at hl
    | cons b ys=>
      have he:=@UnaryOutputEquality.prefixInput_injective (a,stream xs++s) (b,stream ys++t)
        (by simpa only [UnaryOutputEquality.prefixInput,stream,List.append_assoc,List.cons_append] using h)
      have ht:=ih ys s t (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl)
        (congrArg Prod.snd he)
      exact ⟨congrArg₂ List.cons (congrArg Prod.fst he) ht.1,ht.2⟩
end QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
