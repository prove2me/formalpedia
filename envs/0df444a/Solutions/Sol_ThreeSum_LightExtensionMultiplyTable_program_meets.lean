-- Prove2me | solution 1 for ThreeSum.LightExtensionMultiplyTable.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:17.692246+00:00
-- url     : https://prove2.me/submissions/cd594842-da6e-4a3d-8f55-d8bbef0e14b2

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_header_kept
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
open ThreeSum ThreeSum.LightExtensionMultiplyTable
attribute [local instance] ThreeSum.LightExtensionMultiplyTable._p2m_local_instance_2a3ffe096f_5
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionMultiplyTable
theorem _root_.solution {ctx q table depth : ℕ}
    (C : LightExtensionQuotientPredicate.Layout) (μ : ℕ → ℤ)
    (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+8 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q)
    (H : Seg μ ctx (LightExtensionQuotientPredicate.header C))
    (hctx : ctx+10 ≤ table) (hpow : C.powers+(2*C.dim+1) ≤ table)
    (hmod : C.modulus+(C.dim+1) ≤ table)
    (htable : table+q*q ≤ C.a) (hab : C.a+C.dim ≤ C.b) (hbh : C.b+C.dim ≤ C.h)
    (hh : C.h+C.dim ≤ C.remainder) (hr : C.remainder+2*C.dim ≤ C.productWork)
    (hprod : C.productWork+2*C.dim ≤ C.sumWork)
    (hspace : C.sumWork+2*C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim+1, μ (C.modulus+i)=(f i : ℤ))
    (hfBound : ∀ i < C.dim+1, f i < C.p)
    (hword : (word q ctx C.p C.dim C.powers C.a C.b : ℤ) ≤ lim.word)
    (hcellWord : (LightExtensionMultiplyCell.word C q ctx : ℤ) ≤ lim.word)
    (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hspec : ∀ a < q, ∀ b < q,
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b) f)) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=mul a b) :
    Meets lim program 14 depth [q,ctx,C.p,C.dim,C.powers,C.a,C.b,table] μ
      (time q (LightExtensionMultiplyCell.time C q))
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table+x*q+y)=(mul x y : ℤ)) ∧
        Kept μ ν table) := by
  apply meets rfl rfl rfl μ mul hw (by omega) hq (by omega)
    (by omega) (by omega) (by omega) (by omega) hword hmul
  intro x hx y hy ν hν
  have Hν := LightExtensionQuotientPredicate.header_kept H hctx hν
  have hpν (i : ℕ) (hi : i ≤ 2*C.dim) :=
    (hν _ (by omega)).trans (hpowRead i hi)
  have hfν (i : ℕ) (hi : i < C.dim+1) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hc := (LightExtensionMultiplyCell.program_meets C ν f mul hw (by omega) hp hq hx hy
    Hν (by omega) (by omega) (by omega) hab hbh hh hr hprod hspace hpν hfν hfBound hcellWord hspec).append
      [body 13 2 3]
  apply hc.mono (by rfl)
  rintro z ξ ⟨hz,hkeep⟩
  exact ⟨hz,fun a ha => hkeep a (by omega)⟩
end ThreeSum.LightExtensionMultiplyTable
