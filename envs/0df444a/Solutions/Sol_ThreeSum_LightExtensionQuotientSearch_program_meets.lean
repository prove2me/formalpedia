-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientSearch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:12:36.9092+00:00
-- url     : https://prove2.me/submissions/f0ab0d5b-4d97-4f9c-bc90-17199129fd41

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_time_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_word_mono
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_header_kept
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_time_mono
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_word_mono
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionQuotientSearch._p2m_local_instance_7afa0e64b3_11
namespace ThreeSum.LightExtensionQuotientSearch
theorem _root_.solution (C : Layout) {ctx q depth : ℕ}
    (μ : ℕ → ℤ) (x y f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p)
    (H : Seg μ ctx (header C)) (hctx : ctx+10≤C.h)
    (hpowers : C.powers+(2*C.dim+1)≤C.h)
    (hpowRead : ∀ e≤2*C.dim, μ (C.powers+e)=((C.p^e : ℕ) : ℤ))
    (ha : C.a+C.dim≤C.h) (hb : C.b+C.dim≤C.h)
    (hf : C.modulus+(C.dim+1)≤C.h)
    (hh : C.h+C.dim≤C.remainder) (hr : C.remainder+2*C.dim≤C.productWork)
    (hprod : C.productWork+2*C.dim≤C.sumWork)
    (hspace : C.sumWork+2*C.dim≤lim.space)
    (hxRead : ∀ i<C.dim, μ (C.a+i)=(x i : ℤ))
    (hyRead : ∀ i<C.dim, μ (C.b+i)=(y i : ℤ))
    (hfRead : ∀ i<C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hxBound : ∀ i<C.dim, x i<C.p) (hyBound : ∀ i<C.dim, y i<C.p)
    (hfBound : ∀ i<C.dim+1, f i<C.p)
    (hword : (LightExtensionQuotientPredicate.word C.dim C.p q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 12 depth [q,ctx] μ
      (q*q*(LightExtensionQuotientPredicate.time C.dim C.p q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C x y f)) (q*q) : ℤ) ∧
        Kept μ ν C.h) := by
  let I := fun ν : ℕ → ℤ => Kept μ ν C.h
  apply LightPairSearch.program_meets LightExtensionQuotientPredicate.program 0
    (good C x y f) I hq μ (fun _ _ => rfl) hsearchWord (by omega)
  intro u hu v hv ν hν
  have Hν := header_kept H hctx hν
  have hpowν (e : ℕ) (he : e≤2*C.dim) : ν (C.powers+e)=((C.p^e : ℕ) : ℤ) :=
    (hν _ (by omega)).trans (hpowRead e he)
  have hxν (i : ℕ) (hi : i<C.dim) : ν (C.a+i)=(x i : ℤ) :=
    (hν _ (by omega)).trans (hxRead i hi)
  have hyν (i : ℕ) (hi : i<C.dim) : ν (C.b+i)=(y i : ℤ) :=
    (hν _ (by omega)).trans (hyRead i hi)
  have hfν (i : ℕ) (hi : i<C.dim+1) : ν (C.modulus+i)=(f i : ℤ) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hwuv : (LightExtensionQuotientPredicate.word C.dim C.p u v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (word_mono C.dim C.p u v q hu.le hv.le)).trans hword
  have hc := LightExtensionQuotientPredicate.procs.meets (depth := depth+2) C ν x y f
    hw (by omega) hp Hν hctx hpowers hpowν ha hb hf hh hr hprod hspace
    hxν hyν hfν hxBound hyBound hfBound hwuv
  apply hc.mono (time_mono C.dim C.p u v q hu.le hv.le)
  rintro r ξ ⟨hr,hkeep⟩
  refine ⟨?_,?_⟩
  · unfold result LightPolynomialProductCheck.flag at hr
    unfold good
    split_ifs at hr ⊢ <;> first | exact hr | contradiction
  · intro a ha
    exact (hkeep a ha).trans (hν a ha)
end ThreeSum.LightExtensionQuotientSearch
