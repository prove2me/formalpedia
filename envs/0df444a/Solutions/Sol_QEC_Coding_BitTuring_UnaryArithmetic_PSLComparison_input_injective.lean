-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:42.188072+00:00
-- url     : https://prove2.me/submissions/f0931d10-6cbc-4761-8f18-fceff57bae34

import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparisonSupport
import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparison
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
open QEC.Coding.BitTuring.UnaryArithmetic.PSLComparisonSupport
namespace QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison
theorem _root_.solution : Function.Injective input :=by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk a b c d e f g h q ha hb hc hd=>
    cases y with
    | mk a' b' c' d' e' f' g' h' q' ha' hb' hc' hd'=>
      change [a,b,c,d,e,f,g,h,q]=[a',b',c',d',e',f',g',h',q'] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩
      rfl
end QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison
