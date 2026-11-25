-- Prove2me | solution 1 for PI.WGL.LTC.word_clause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:52.413439+00:00
-- url     : https://prove2.me/submissions/cacea70c-e270-49a6-81f2-9129a924e66c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Theorems.Thm_PI_WGL_LTC_exp_bidet
import Theorems.Thm_PI_WGL_LTC_exp_M
import Theorems.Thm_PI_WGL_LTC_polarization_of_constant
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_LTA_applyWord_comb
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
open PI PI.WGL PI.WGL.LTC
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM
namespace PI.WGL.LTC
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) :
    ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
      applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
      applyWord ℤ (liftWord h w) (Mlift h lam sg sz hsz L I) =
        d.sum (fun J c => c • Mlift h lam sg sz hsz L J) := by
  classical
  refine ⟨twd sz w (Finsupp.single I 1), ?_, ?_⟩
  · have hmap : w.map (fun x => (id x.1, id x.2.1, x.2.2)) = w := by
      induction w with
      | nil => rfl
      | cons x w ih => simp
    have h1 := applyWord_comb id sz (fun k ρ => initMinor ℤ (n := n) ρ (hsz k)) (exp_bidet sz hsz) 1
      (fun a b _ => by simp) w hw (Finsupp.single I 1)
    rw [hmap, Finsupp.linearCombination_single, one_smul] at h1
    simp only [one_mul, Finsupp.linearCombination_apply] at h1
    unfold bideterminant
    exact h1
  · have h2 := applyWord_comb (eRow h) sz
      (fun k ρ => if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (exp_M h sz hsz L) (C0 h lam sg) (fun a b hab => polarization_of_constant h lam sg a b hab) w hw (Finsupp.single I 1)
    rw [Finsupp.linearCombination_single, one_smul] at h2
    simp only [Finsupp.linearCombination_apply] at h2
    unfold Mlift
    exact h2
end PI.WGL.LTC
