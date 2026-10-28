-- Prove2me | solution 1 for SGHMCOpt.Euler.lemma_25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:28:23.84491+00:00
-- url     : https://prove2.me/submissions/24f474cf-0611-402b-8db3-13b04b5b433d

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

namespace Aux_SGHMC25
open SGHMCOpt.Euler

lemma hasDerivAt_ray {d : ℕ} (G : E d → ℝ) (hG : Differentiable ℝ G) (x : E d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => G (s • x)) (inner ℝ (gradient G (t • x)) x) t := by
  have h3 : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have h := (hG (t • x)).hasFDerivAt.comp_hasDerivAt t h3
  have e : inner ℝ (gradient G (t • x)) x = fderiv ℝ G (t • x) x := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e]
  exact h

end Aux_SGHMC25

open SGHMCOpt.Euler Aux_SGHMC25 in
theorem solution {d : ℕ} {𝒵 : Type*} [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (p : Params)
    (hloss : LossAssumption f p) (x : E d) (ζ : 𝒵) :
    ‖gradient (fun y => f y ζ) x‖ ≤ p.M * ‖x‖ + p.B ∧
      p.m / 3 * ‖x‖ ^ 2 - p.b / 2 * Real.log 3 ≤ f x ζ ∧
      f x ζ ≤ p.M / 2 * ‖x‖ ^ 2 + p.B * ‖x‖ + p.A0 := by
  set G : E d → ℝ := fun y => f y ζ with hGdef
  have hG : Differentiable ℝ G := (hloss.contDiff ζ).differentiable one_ne_zero
  have hray := hasDerivAt_ray G hG x
  have hsm : ∀ w v, ‖gradient G w - gradient G v‖ ≤ p.M * ‖w - v‖ := hloss.smooth ζ
  have hg0 : ‖gradient G 0‖ ≤ p.B := hloss.grad_zero ζ
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hsm x 0
    simp only [sub_zero] at h1
    calc ‖gradient G x‖ = ‖(gradient G x - gradient G 0) + gradient G 0‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖gradient G x - gradient G 0‖ + ‖gradient G 0‖ := norm_add_le _ _
      _ ≤ p.M * ‖x‖ + p.B := add_le_add h1 hg0
  · -- lower bound
    set c : ℝ := (Real.sqrt 3)⁻¹ with hc
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs3p : 0 < Real.sqrt 3 := by positivity
    have hc0 : 0 < c := inv_pos.2 hs3p
    have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have hc2 : c ^ 2 = 1 / 3 := by rw [hc, inv_pow, hs3]; norm_num
    have hlogc : Real.log c = -(Real.log 3 / 2) := by
      rw [hc, Real.log_inv, Real.log_sqrt (by norm_num)]
    have hψ : ∀ s, 0 < s → HasDerivAt
        (fun s : ℝ => G (s • x) - p.m / 2 * s ^ 2 * ‖x‖ ^ 2 + p.b * Real.log s)
        (inner ℝ (gradient G (s • x)) x - p.m * s * ‖x‖ ^ 2 + p.b * s⁻¹) s := by
      intro s hs
      have h := ((hray s).sub (((hasDerivAt_pow 2 s).const_mul (p.m / 2)).mul_const
        (‖x‖ ^ 2))).add ((Real.hasDerivAt_log hs.ne').const_mul p.b)
      refine h.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp
    have hmono : MonotoneOn
        (fun s : ℝ => G (s • x) - p.m / 2 * s ^ 2 * ‖x‖ ^ 2 + p.b * Real.log s)
        (Set.Icc c 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c 1)
        (f' := fun s => inner ℝ (gradient G (s • x)) x - p.m * s * ‖x‖ ^ 2 + p.b * s⁻¹)
      · intro s hs
        exact (hψ s (lt_of_lt_of_le hc0 hs.1)).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hψ s (hc0.trans hs.1)).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs0 : 0 < s := hc0.trans hs.1
        have hdis : p.m * ‖s • x‖ ^ 2 - p.b ≤ inner ℝ (s • x) (gradient G (s • x)) :=
          hloss.dissipative ζ (s • x)
        rw [inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, real_inner_comm] at hdis
        simp only [conj_trivial] at hdis
        have heq : inner ℝ (gradient G (s • x)) x - p.m * s * ‖x‖ ^ 2 + p.b * s⁻¹ =
            (s * inner ℝ (gradient G (s • x)) x - p.m * (s * ‖x‖) ^ 2 + p.b) / s := by
          field_simp
        show 0 ≤ inner ℝ (gradient G (s • x)) x - p.m * s * ‖x‖ ^ 2 + p.b * s⁻¹
        rw [heq]
        apply div_nonneg _ hs0.le
        linarith
    have hle := hmono ⟨le_rfl, hc1⟩ ⟨hc1, le_rfl⟩ hc1
    simp only [one_smul, one_pow, mul_one, Real.log_one, mul_zero, add_zero] at hle
    rw [hc2, hlogc] at hle
    have hnn : 0 ≤ G (c • x) := hloss.nonneg _ _
    show p.m / 3 * ‖x‖ ^ 2 - p.b / 2 * Real.log 3 ≤ G x
    nlinarith
  · -- upper bound
    set c0 : ℝ := inner ℝ (gradient G 0) x with hc0
    have hψ : ∀ s, HasDerivAt
        (fun s : ℝ => G (s • x) - s * c0 - p.M / 2 * s ^ 2 * ‖x‖ ^ 2)
        (inner ℝ (gradient G (s • x)) x - c0 - p.M * s * ‖x‖ ^ 2) s := by
      intro s
      have h := ((hray s).sub (hasDerivAt_mul_const c0)).sub
        (((hasDerivAt_pow 2 s).const_mul (p.M / 2)).mul_const (‖x‖ ^ 2))
      refine h.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp
    have hanti : AntitoneOn
        (fun s : ℝ => G (s • x) - s * c0 - p.M / 2 * s ^ 2 * ‖x‖ ^ 2) (Set.Icc 0 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
        (f' := fun s => inner ℝ (gradient G (s • x)) x - c0 - p.M * s * ‖x‖ ^ 2)
      · intro s _
        exact (hψ s).continuousAt.continuousWithinAt
      · intro s _
        exact (hψ s).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hs0 : 0 < s := hs.1
        have h1 := hsm (s • x) 0
        rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at h1
        have h2 : inner ℝ (gradient G (s • x) - gradient G 0) x ≤
            ‖gradient G (s • x) - gradient G 0‖ * ‖x‖ := real_inner_le_norm _ _
        rw [inner_sub_left] at h2
        have h3 : ‖gradient G (s • x) - gradient G 0‖ * ‖x‖ ≤ p.M * (s * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        show inner ℝ (gradient G (s • x)) x - c0 - p.M * s * ‖x‖ ^ 2 ≤ 0
        nlinarith
    have hle := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
    simp only [one_smul, one_mul, one_pow, zero_smul, zero_mul, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hle
    have hA := hloss.bound_zero ζ
    have hc0le : c0 ≤ p.B * ‖x‖ := by
      calc c0 ≤ ‖gradient G 0‖ * ‖x‖ := real_inner_le_norm _ _
        _ ≤ p.B * ‖x‖ := mul_le_mul_of_nonneg_right hg0 (norm_nonneg _)
    have hA' : G 0 ≤ p.A0 := (le_abs_self _).trans hA
    show G x ≤ p.M / 2 * ‖x‖ ^ 2 + p.B * ‖x‖ + p.A0
    linarith
