-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.scalar_safe_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:00.771434+00:00
-- url     : https://prove2.me/submissions/c7f7336a-ed48-418e-95b2-0452d0626194

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Theorems.Thm_ThreeSum_LightSwitchScalar_pow_cost_left
import Theorems.Thm_ThreeSum_LightSwitchScalar_pow_cost_right
import Theorems.Thm_ThreeSum_LightSwitchScalar_scalar_bound
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
theorem _root_.solution {lim : Limits} {B : ℕ} (hB : 2 ≤ B) (σ : State)
    (hvars : ∀ i, |σ.loc i| ≤ (B : ℤ)) (e : Expr) (he : Small B e)
    (hword : ((B^e.cost : ℕ) : ℤ) ≤ lim.word) : e.Safe lim σ := by
  induction e with
  | const n =>
    have hn : (n : ℤ) ≤ (B : ℤ) := Int.ofNat_le.mpr he
    simpa [Expr.Safe,Expr.cost] using hn.trans (by simpa [Expr.cost] using hword)
  | var i => trivial
  | load e ih => exact False.elim he
  | op o a b ia ib =>
    have hwA : ((B^a.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (pow_cost_left B a.cost b.cost (by omega))).trans hword
    have hwB : ((B^b.cost : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (pow_cost_right B a.cost b.cost (by omega))).trans hword
    exact ⟨ia he.1 hwA,ib he.2 hwB,(scalar_bound hB σ hvars (.op o a b) he).trans hword⟩
end ThreeSum.LightSwitchScalar
