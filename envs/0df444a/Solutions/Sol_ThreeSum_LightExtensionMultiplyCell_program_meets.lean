-- Prove2me | solution 1 for ThreeSum.LightExtensionMultiplyCell.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:19:34.078698+00:00
-- url     : https://prove2.me/submissions/d6589b2c-dd14-4df7-976d-64fe71707d44

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
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
open ThreeSum ThreeSum.LightExtensionMultiplyCell
open Light LightExtensionQuotientPredicate
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
attribute [local instance] ThreeSum.LightExtensionMultiplyCell._p2m_local_instance_2d48f70718_8
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionMultiplyCell
theorem _root_.solution {ctx q x y : ℕ} (C : Layout)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+7 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (hx : x < q) (hy : y < q)
    (H : Seg μ ctx (header C)) (hctx : ctx+10 ≤ C.a)
    (hpow : C.powers+(2*C.dim+1) ≤ C.a)
    (hmod : C.modulus+(C.dim+1) ≤ C.a)
    (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word C q ctx : ℤ) ≤ lim.word)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (digits C.p a) (digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b)
 :
    Meets lim program 13 depth [x,y,ctx,C.p,C.dim,C.powers,C.a,C.b,q] μ (time C q)
      (fun z ν => z=(mul x y : ℤ) ∧ Kept μ ν C.a) := by
  apply meets C rfl rfl rfl rfl μ f mul hw hd hp hq hx hy H hctx hpow hmod
    hab hbh hh hr hprod hspace hpowRead hfRead hfBound hword hspec
  intro ν Hν hpowν hxν hyν hfν
  have hsw : (LightExtensionQuotientPredicate.word C.dim C.p q q : ℤ) ≤ lim.word := by
    unfold word at hword; omega
  have hsearchw : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word := by
    unfold word at hword; omega
  have digBound (code i : ℕ) : digits C.p code i < C.p := Nat.mod_lt _ (by omega)
  exact (LightExtensionQuotientSearch.program_meets C ν (digits C.p x) (digits C.p y) f hw
    (by omega) hq hp Hν (by omega) (by omega) hpowν (by omega) hbh (by omega)
    hh hr hprod hspace hxν hyν hfν (fun i _ => digBound x i)
    (fun i _ => digBound y i) hfBound hsw hsearchw).append [body 1 12 2]
end ThreeSum.LightExtensionMultiplyCell
