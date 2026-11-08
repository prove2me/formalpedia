-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse4_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:50:00.578775+00:00
-- url     : https://prove2.me/submissions/3d421f9d-4cd6-4b98-8408-1af354c2e35e

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_pushed_append
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_field_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (xs:List ℕ) (k:Fin 5) (hk:k.val+xs.length=4)
 (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[(stream xs).length]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (stream xs++O) H C B))=
 some (cfg P 9 f (if xs=[] then h else some false) I O H (pushed f (stream xs) C) B):=by
 induction xs generalizing k h C with
 |nil=>
  have he:⟨5+k.val,by omega⟩=(9:Fin 15):=by
   apply Fin.ext;change 5+k.val=9;simp only [List.length_nil] at hk;omega
  simp [stream,pushed,he]
 |cons a xs ih=>
  have hl:k.val<4:=by simp only [List.length_cons] at hk;omega
  let j:Fin 5:=⟨k.val+1,by omega⟩
  let kk:Fin 4:=⟨k.val,hl⟩
  have ht:=ih j (by dsimp [j];simp only [List.length_cons] at hk;omega) (some false)
   (pushed f (unary a++[false]) C)
  have hs:(stream (a::xs)).length=(stream xs).length+(a+1):=by
   simp only [stream,List.length_append,List.length_cons,unary_length];omega
  rw [hs,Function.iterate_add_apply]
  have he:stream (a::xs)++O=unary a++false::(stream xs++O):=by
   simp only [stream,List.append_assoc,List.cons_append]
  rw [he]
  have hf:=field_run P hio kk f h a I (stream xs++O) H C B
  have hj:(⟨6+kk.val,by omega⟩:Fin 15)=⟨5+j.val,by omega⟩:=by apply Fin.ext;dsimp [kk,j];omega
  change (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[a+1]
   (some (cfg P ⟨5+k.val,by omega⟩ f h I (unary a++false::(stream xs++O)) H C B))=_ at hf
  rw [hf,hj,ht]
  have hp:pushed f (stream (a::xs)) C=pushed f (stream xs) (pushed f (unary a++[false]) C):=by
   rw [show stream (a::xs)=(unary a++[false])++stream xs by simp [stream,List.append_assoc],pushed_append]
  rw [hp]
  cases xs <;>simp
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
