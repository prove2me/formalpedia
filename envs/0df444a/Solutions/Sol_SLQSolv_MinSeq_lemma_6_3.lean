-- Prove2me | solution 1 for SLQSolv.MinSeq.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:56:51.892996+00:00
-- url     : https://prove2.me/submissions/21eeb610-413a-4b62-be3c-307104013670

import Mathlib

open Filter Topology
open scoped ENNReal InnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (θ : H) (θs : ℕ → H) :
    ((∀ y : H, Tendsto (fun k => ⟪θs k, y⟫_ℝ) atTop (𝓝 ⟪θ, y⟫_ℝ)) →
        ‖θ‖ₑ ≤ Filter.liminf (fun k => ‖θs k‖ₑ) atTop) ∧
      (Tendsto θs atTop (𝓝 θ) ↔
        Tendsto (fun k => ‖θs k‖) atTop (𝓝 ‖θ‖) ∧
          ∀ y : H, Tendsto (fun k => ⟪θs k, y⟫_ℝ) atTop (𝓝 ⟪θ, y⟫_ℝ)) := by
  constructor
  · intro hw
    apply le_of_forall_lt_imp_le_of_dense
    intro b hb
    have hbtop : b ≠ ⊤ := ne_top_of_lt hb
    rw [← ofReal_norm, ENNReal.lt_ofReal_iff_toReal_lt hbtop] at hb
    set t := b.toReal with ht
    have hθ0 : 0 < ‖θ‖ := lt_of_le_of_lt ENNReal.toReal_nonneg hb
    have hlim := hw θ
    rw [real_inner_self_eq_norm_sq] at hlim
    have hev : ∀ᶠ k in atTop, t * ‖θ‖ < ⟪θs k, θ⟫_ℝ :=
      hlim.eventually (lt_mem_nhds (by nlinarith))
    have hev' : ∀ᶠ k in atTop, b ≤ ‖θs k‖ₑ := hev.mono fun k hk => by
      have h1 : ⟪θs k, θ⟫_ℝ ≤ ‖θs k‖ * ‖θ‖ := real_inner_le_norm _ _
      have h2 : t < ‖θs k‖ := lt_of_mul_lt_mul_right (by linarith) hθ0.le
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hbtop]
      exact ENNReal.ofReal_le_ofReal h2.le
    exact Filter.le_liminf_of_le (h := hev')
  · constructor
    · intro h
      exact ⟨(continuous_norm.tendsto θ).comp h, fun y => h.inner tendsto_const_nhds⟩
    · rintro ⟨hn, hw⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun k => ‖θs k‖ ^ 2 - 2 * ⟪θs k, θ⟫_ℝ + ‖θ‖ ^ 2) atTop
          (𝓝 (‖θ‖ ^ 2 - 2 * ⟪θ, θ⟫_ℝ + ‖θ‖ ^ 2)) :=
        ((hn.pow 2).sub (tendsto_const_nhds.mul (hw θ))).add tendsto_const_nhds
      rw [real_inner_self_eq_norm_sq] at h1
      have h2 : Tendsto (fun k => ‖θs k - θ‖ ^ 2) atTop (𝓝 0) := by
        have e : (fun k => ‖θs k - θ‖ ^ 2) = fun k => ‖θs k‖ ^ 2 - 2 * ⟪θs k, θ⟫_ℝ + ‖θ‖ ^ 2 :=
          funext fun k => norm_sub_sq_real _ _
        rw [e]
        convert h1 using 2
        ring
      have h3 := h2.sqrt
      simp only [Real.sqrt_zero] at h3
      convert h3 using 2 with k
      rw [Real.sqrt_sq (norm_nonneg _)]
