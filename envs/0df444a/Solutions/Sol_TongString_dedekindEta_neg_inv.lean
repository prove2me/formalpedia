-- Prove2me | solution 1 for TongString.dedekindEta_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:26:40.736802+00:00
-- url     : https://prove2.me/submissions/17814b0e-6e21-433e-b5c8-bde898ae374d

import Mathlib
import Definitions.Def_TongString_dedekind_eta

open Complex in
lemma p89_eta_eq (z : ℂ) : TongString.dedekindEta z = ModularForm.eta z := by
  unfold TongString.dedekindEta ModularForm.eta
  have hq : Function.Periodic.qParam 24 z = Complex.exp (2 * Real.pi * I * z / 24) := by
    rw [Function.Periodic.qParam]; congr 1
  have hp : ∀ n : ℕ, ModularForm.eta_q n z
      = Complex.exp (2 * Real.pi * I * ((n : ℂ) + 1) * z) := fun n => ModularForm.eta_q_eq_cexp n z
  rw [hq]
  simp only [hp]

open Complex in
lemma p89_cpow (τ : ℂ) (hτ : 0 < τ.im) :
    (-I * τ) ^ (1 / 2 : ℂ) = (Complex.sqrt I)⁻¹ * Complex.sqrt τ := by
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h] at hτ; simp at hτ
  have harg : 0 ≤ arg τ := arg_nonneg_iff.2 hτ.le
  have harg2 : arg τ ≤ Real.pi := arg_le_pi τ
  have hlog : log (-I * τ) = log (-I) + log τ := by
    rw [log_mul_eq_add_log_iff (by simp) hτ0]
    rw [arg_neg_I]
    constructor <;> linarith [Real.pi_pos]
  rw [_root_.sqrt_eq_exp I_ne_zero, _root_.sqrt_eq_exp hτ0,
    cpow_def_of_ne_zero (mul_ne_zero (by simp) hτ0), hlog, log_I, log_neg_I,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

open Complex in
theorem solution (τ : ℂ) (hτ : 0 < τ.im) :
    TongString.dedekindEta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * TongString.dedekindEta τ := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv (show τ ∈ UpperHalfPlane.upperHalfPlaneSet from hτ)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [p89_eta_eq, p89_eta_eq, h, p89_cpow τ hτ]
  ring
