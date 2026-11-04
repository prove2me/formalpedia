-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:08:04.016457+00:00
-- url     : https://prove2.me/submissions/a732cc9a-8dce-4c9a-8625-60e67d01a20c

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Theorems.Thm_ThreeSum_LightSwitchScalar_sum_pow_le
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000
namespace ThreeSum.LightSwitchScalar
theorem _root_.solution {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e) :
    |e.val σ| ≤ ((B^e.cost : ℕ) : ℤ) := by
  induction e with
  | const n => simpa [Expr.val,Expr.cost,Int.abs_natCast] using (Int.ofNat_le.mpr he)
  | var i => simpa [Expr.val,Expr.cost] using hvars i
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have hadd : ((B^a.cost : ℕ) : ℤ)+(B^b.cost : ℕ) ≤
        ((B^(a.cost+b.cost+1) : ℕ) : ℤ) := by exact_mod_cast sum_pow_le hB a.cost b.cost
    have hprod : ((B^a.cost : ℕ) : ℤ)*(B^b.cost : ℕ) ≤
        ((B^(a.cost+b.cost+1) : ℕ) : ℤ) := by
      have hh : B^a.cost*B^b.cost ≤ B^(a.cost+b.cost+1) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast hh
    cases o with
    | add => exact (abs_add_le _ _).trans ((add_le_add ha hb).trans hadd)
    | sub =>
      change |a.val σ-b.val σ| ≤ _
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans ((add_le_add ha (by simpa only [abs_neg] using hb)).trans hadd)
    | mul =>
      change |a.val σ*b.val σ| ≤ _
      rw [abs_mul]
      exact (mul_le_mul ha hb (abs_nonneg _) (by positivity)).trans hprod
end ThreeSum.LightSwitchScalar
