-- Prove2me | solution 1 for PI.PolynomialProperness.second_order_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:06.034945+00:00
-- url     : https://prove2.me/submissions/74f41386-0ddb-4f75-b0c5-60d865c9c1f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_det_ut
import Theorems.Thm_PI_PolynomialProperness_CB_det_lt
import Theorems.Thm_PI_PolynomialProperness_CB_inv_entry_bound
import Theorems.Thm_PI_PolynomialProperness_CB_mx_of_entry
import Theorems.Thm_P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4
import Theorems.Thm_PI_PolynomialProperness_CB_kap_ge
import Theorems.Thm_PI_PolynomialProperness_CB_factors_bound
import Theorems.Thm_PI_PolynomialProperness_GN_mx_le_iff
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
open CB
namespace PI.PolynomialProperness
theorem _root_.solution : MonomialFactorizationBound := by
  intro m P hP
  obtain ⟨w, d, hd, hPeq⟩ := hP
  have hPu : IsUnit P.det := by rw [hPeq]; exact isUnit_det_monomialMatrix' w d hd
  cases m with
  | zero =>
    refine ⟨0, fun l _ u' _ => ?_⟩
    have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, mx M ≤ 0 :=
      fun M => (GN.mx_le_iff M le_rfl).2 fun i => i.elim0
    simp only [zero_mul]
    exact ⟨h0 _, h0 _, h0 _, h0 _⟩
  | succ n =>
    have hK0 : 0 ≤ Kc (n + 1) P := by
      unfold Kc
      have := kap_ge (n + 1) P
      have := GN.mx_nonneg P; have := GN.mx_nonneg P⁻¹
      have : (0 : ℝ) ≤ 1 + ((n + 1 : ℕ) : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
      have : (0 : ℝ) ≤ kap (n + 1) P := by linarith
      positivity
    refine ⟨n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P, fun l hl u' hu' => ?_⟩
    obtain ⟨hbu, hbl⟩ := factors_bound hPu hl hu'
    set X := mx (l * P * u') with hXdef
    have hX : 0 ≤ X := GN.mx_nonneg _
    have hY : 0 ≤ Kc (n + 1) P * (1 + X) ^ (n + 1) := by positivity
    have hfn : (0 : ℝ) ≤ n.factorial * Kc (n + 1) P ^ n := by positivity
    have hCge : Kc (n + 1) P ≤ n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P := by linarith
    have hmain : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ (n + 1) := by
      intro M hM
      refine mx_of_entry M (by positivity) fun i j => (hM i j).trans ?_
      exact mul_le_mul_of_nonneg_right hCge (by positivity)
    have hinv : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M.det = 1 →
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M⁻¹ ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ ((n + 1 - 1) * (n + 1)) := by
      intro M hdet hM
      have e : (1 + X) ^ ((n + 1 - 1) * (n + 1)) = ((1 + X) ^ (n + 1)) ^ n := by
        rw [Nat.add_sub_cancel, ← pow_mul, mul_comm]
      rw [e]
      refine mx_of_entry _ (by positivity) fun i j => (inv_entry_bound M hdet hM i j).trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine ⟨hmain l hbl, hmain u' hbu, hinv l (det_lt hl.1) hbl, hinv u' (det_ut hu') hbu⟩
end PI.PolynomialProperness
