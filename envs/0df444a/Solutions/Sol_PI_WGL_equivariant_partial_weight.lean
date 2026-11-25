-- Prove2me | solution 1 for PI.WGL.equivariant_partial_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:42.616608+00:00
-- url     : https://prove2.me/submissions/bf5e6247-6098-4499-93cd-30e39f719556

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_coeff_sqAct_diag
import Theorems.Thm_PI_WGL_EqvWt_weight_rowW_apply
import Theorems.Thm_PI_WGL_EqvWt_two_zpow_inj
import Theorems.Thm_PI_WGL_EqvWt_coeff_eq_of_eqv
import Theorems.Thm_PI_WGL_EqvWt_equivariant_last_degree_coeff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open EqvWt
namespace PI.WGL
theorem _root_.solution : EqvRowWt := by
  intro n N h lam mu hI φ hφ ω s hs hω
  subst h
  intro m hm
  funext a
  rw [weight_rowW_apply]
  induction a using Fin.lastCases with
  | last =>
    have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
    unfold liftWt
    rw [dif_neg (by simp)]
    show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
    omega
  | cast i =>
    have hi := i.isLt
    let t : Fin n → ℂˣ := fun j => if j = i then Units.mk0 (2 : ℂ) two_ne_zero else 1
    have hp : ∀ f : Fin n → ℕ, ∏ j, (t j : ℂ) ^ f j = 2 ^ f i := by
      intro f
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro j _ hj
        simp [t, hj]
      · simp
    have hp0 : ∏ j, (t j : ℂ) = 2 := by simpa using hp (fun _ => 1)
    have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
        ((∏ j, (t j : ℂ)) ^ mu.detShift * ∏ j, (t j : ℂ) ^ ω j) • s := by
      ext m'
      rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
      by_cases h0 : coeff m' s = 0
      · simp [h0]
      · have hw := hω h0
        have hr : ∀ j, rowDeg m' j = ω j := fun j => by rw [← weight_rowW_apply, hw]
        simp only [hr]
        ring
    have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
    rw [hp0, hp (fun j => rowDeg m (Fin.castSucc j)), hp ω] at h1
    rw [← zpow_natCast, ← zpow_natCast (2 : ℂ) (ω i), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
    have E := two_zpow_inj h1
    have hle : lam.detShift ≤ mu.detShift := by
      have h2 := (hI ⟨n - 1, by omega⟩).2
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < n + 1), dif_pos (by omega : 0 < n)]
      exact (le_of_eq (congrArg lam.w (Fin.ext (by show n + 1 - 1 = n - 1 + 1; omega)))).trans h2
    unfold liftWt
    rw [dif_pos (by simp)]
    simp only [Fin.coe_castSucc, Fin.eta]
    omega
end PI.WGL
