-- Prove2me | solution 1 for ProxBundle.GPB.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:49:57.439764+00:00
-- url     : https://prove2.me/submissions/a392381f-dabc-47b1-b950-fabd9d0d50bb

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Theorems.Thm_ProxBundle_GPB_eq_7

open ProxBundle.GPB
open scoped InnerProductSpace RealInnerProductSpace

lemma gpb_l46_sq_comb {n : ℕ} (x u c : E n) (t : ℝ) :
    ‖(1 - t) • x + t • u - c‖ ^ 2 =
      (1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2 := by
  have h1 : (1 - t) • x + t • u - c = (1 - t) • (x - c) + t • (u - c) := by module
  have h2 : u - x = (u - c) - (x - c) := by abel
  rw [h1, h2]
  generalize x - c = p
  generalize u - c = q
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_comm q]
  ring

/-- Quadratic growth of a `(μ + 1/λ)`-strongly convex proximal objective at its minimizer
(Theorem 5.25(b) of Beck, as used in (46) and (52)). -/
lemma gpb_l46_qgrowth {n : ℕ} (D : Set (E n)) (μ lam : ℝ) (G : E n → ℝ) (c x : E n)
    (hG : StrongConvexOn D μ G) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hx : x ∈ D)
    (hmin : ∀ u ∈ D, G x + ‖x - c‖ ^ 2 / (2 * lam) ≤ G u + ‖u - c‖ ^ 2 / (2 * lam))
    (u : E n) (hu : u ∈ D) :
    G x + ‖x - c‖ ^ 2 / (2 * lam) + (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 ≤
      G u + ‖u - c‖ ^ 2 / (2 * lam) := by
  set K := (μ + 1 / lam) / 2 * ‖u - x‖ ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (1 - t) * K ≤ (G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam)) := by
    intro t ht0 ht1
    have hw := hG.2 hx hu (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    have hwD : (1 - t) • x + t • u ∈ D := hG.1 hx hu (by linarith) ht0.le (by ring)
    have hm := hmin _ hwD
    rw [gpb_l46_sq_comb] at hm
    simp only [smul_eq_mul] at hw
    rw [norm_sub_rev x u] at hw
    have h : 0 ≤ t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
        - (1 - t) * K) := by
      rw [hKdef]
      have e : t * ((G u + ‖u - c‖ ^ 2 / (2 * lam)) - (G x + ‖x - c‖ ^ 2 / (2 * lam))
          - (1 - t) * ((μ + 1 / lam) / 2 * ‖u - x‖ ^ 2)) =
          (t * G u + (1 - t) * G x - (1 - t) * t * (μ / 2 * ‖u - x‖ ^ 2) -
              G ((1 - t) • x + t • u)) +
          (G ((1 - t) • x + t • u) +
            ((1 - t) * ‖x - c‖ ^ 2 + t * ‖u - c‖ ^ 2 - t * (1 - t) * ‖u - x‖ ^ 2) /
              (2 * lam) - (G x + ‖x - c‖ ^ 2 / (2 * lam))) := by
        field_simp
        ring
      rw [e]
      have := hw
      linarith
    have := (mul_nonneg_iff_of_pos_left ht0).mp h
    linarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hKδ : 0 < K + δ := by linarith
  have ht0 : 0 < δ / (K + δ) := by positivity
  have ht1 : δ / (K + δ) ≤ 1 := by rw [div_le_one hKδ]; linarith
  have h := key _ ht0 ht1
  have h2 : δ / (K + δ) * K ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hKδ]; nlinarith
  have e : (1 - δ / (K + δ)) * K = K - δ / (K + δ) * K := by ring
  linarith

theorem solution {n : ℕ} (P : Instance n) (μ Mbar Lbar lam ε τ : ℝ)
    (x0 : E n) (R : Run n)
    (hμ : 0 ≤ μ) (hM : 0 ≤ Mbar) (hL : 0 ≤ Lbar)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mbar Lbar)
    (hlam : 0 < lam) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (h29 : Cond29 μ lam ε τ Mbar Lbar)
    (hx0 : x0 ∈ P.D) (hrun : IsRun P μ lam ε τ x0 R)
    (j : ℕ) (hj : 1 ≤ j) (hnull : ε / 2 < R.t P lam j) :
    R.t P lam (j + 1) - ε / 4 ≤ τ * (R.t P lam j - ε / 4) := by
  have h7 := ProxBundle.GPB.eq_7 P μ Mbar Lbar hμ hM hL hA1 hA3
  obtain ⟨-, hnullbr, hprox1, -, hymin1⟩ := hrun.2.2 (j + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hnullbr
  obtain ⟨hxc, -, -, Γb, hΓbconv, hΓbx, hΓbprox, hlow⟩ := hnullbr hnull
  obtain ⟨-, -, hproxj, ⟨i, hi, hyj⟩, -⟩ := hrun.2.2 j hj
  have hxjD : R.x j ∈ P.D := hproxj.1
  have hxj1D : R.x (j + 1) ∈ P.D := hprox1.1
  have hy1 : P.φ (R.y (j + 1)) ≤ P.φ (R.y j) := by rw [hyj]; exact hymin1 i (by omega)
  have hy2 : P.φ (R.y (j + 1)) ≤ P.φ (R.x (j + 1)) := hymin1 (j + 1) le_rfl
  have htj : R.t P lam j = P.φ (R.y j) -
      (R.Γ j (R.x j) + ‖R.x j - R.xc j‖ ^ 2 / (2 * lam)) := by
    unfold Run.t Run.m; rw [if_neg (by omega)]
  have htj1 : R.t P lam (j + 1) = P.φ (R.y (j + 1)) -
      (R.Γ (j + 1) (R.x (j + 1)) + ‖R.x (j + 1) - R.xc j‖ ^ 2 / (2 * lam)) := by
    unfold Run.t Run.m; rw [if_neg (by omega), hxc]
  set c := R.xc j
  set a := ‖R.x (j + 1) - R.x j‖ with ha
  -- (52) with u = x_{j+1}
  have hq := gpb_l46_qgrowth P.D μ lam Γb c (R.x j) hΓbconv hlam hμ hxjD hΓbprox.2
    (R.x (j + 1)) hxj1D
  rw [hΓbx] at hq
  -- (50) at x_{j+1}
  have hlo := hlow (R.x (j + 1)) hxj1D
  -- (7) at (x_{j+1}, x_j)
  have he7 := h7 (R.x (j + 1)) hxj1D (R.x j) hxjD
  rw [← ha] at he7 hq
  unfold Instance.φ at hy1 hy2 htj htj1
  -- (54)
  have hc29 : (1 - τ) * (8 * lam * (Mbar ^ 2 + ε * Lbar)) ≤ τ * ((1 + lam * μ) * ε) := by
    unfold Cond29 at h29
    have h1τ : 0 < 1 - τ := by linarith
    rw [div_le_div_iff₀ (by positivity) h1τ] at h29
    linarith
  have hQ : (1 - τ) * (Lbar / 2 + 4 * Mbar ^ 2 / ε) * a ^ 2 ≤
      τ * ((μ + 1 / lam) / 2 * a ^ 2) := by
    have e : τ * ((μ + 1 / lam) / 2) - (1 - τ) * (Lbar / 2 + 4 * Mbar ^ 2 / ε) =
        (τ * ((1 + lam * μ) * ε) - (1 - τ) * (8 * lam * (Mbar ^ 2 + ε * Lbar))) /
          (2 * lam * ε) + (1 - τ) * (7 / 2 * Lbar) := by
      field_simp
      ring
    have h1 : 0 ≤ τ * ((μ + 1 / lam) / 2) - (1 - τ) * (Lbar / 2 + 4 * Mbar ^ 2 / ε) := by
      rw [e]
      have : 0 ≤ (τ * ((1 + lam * μ) * ε) - (1 - τ) * (8 * lam * (Mbar ^ 2 + ε * Lbar))) /
          (2 * lam * ε) := div_nonneg (by linarith) (by positivity)
      have : 0 ≤ (1 - τ) * (7 / 2 * Lbar) := mul_nonneg (by linarith) (by positivity)
      linarith
    have := mul_nonneg h1 (sq_nonneg a)
    linarith
  -- a² − 2ab ≥ −b² step of (57)
  have hsq : -(ε / 4) ≤ 4 * Mbar ^ 2 / ε * a ^ 2 - 2 * Mbar * a := by
    have e : 4 * Mbar ^ 2 / ε * a ^ 2 - 2 * Mbar * a + ε / 4 = (2 * Mbar * a - ε / 2) ^ 2 / ε := by
      field_simp
      ring
    have : 0 ≤ (2 * Mbar * a - ε / 2) ^ 2 / ε := by positivity
    linarith
  -- assemble (53) and (57)
  unfold Instance.ellf at he7 hlo
  have h1τ : 0 ≤ 1 - τ := by linarith
  have hA : τ * (Γb (R.x (j + 1)) + ‖R.x (j + 1) - c‖ ^ 2 / (2 * lam)) ≥
      τ * (R.Γ j (R.x j) + ‖R.x j - c‖ ^ 2 / (2 * lam)) + τ * ((μ + 1 / lam) / 2 * a ^ 2) := by
    have := mul_le_mul_of_nonneg_left hq hτ0.le
    linarith
  have hB : (1 - τ) * (P.f (R.x (j + 1)) + P.h (R.x (j + 1))) - (1 - τ) * (ε / 4) ≤
      (1 - τ) * (P.f (R.x j) + ⟪P.f' (R.x j), R.x (j + 1) - R.x j⟫ + P.h (R.x (j + 1))) +
        (1 - τ) * (Lbar / 2 + 4 * Mbar ^ 2 / ε) * a ^ 2 := by
    have : P.f (R.x (j + 1)) + P.h (R.x (j + 1)) - ε / 4 ≤
        (P.f (R.x j) + ⟪P.f' (R.x j), R.x (j + 1) - R.x j⟫ + P.h (R.x (j + 1))) +
          (Lbar / 2 + 4 * Mbar ^ 2 / ε) * a ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left this h1τ
    linarith
  have hC : 0 ≤ (1 - τ) * (‖R.x (j + 1) - c‖ ^ 2 / (2 * lam)) := by positivity
  have hD : τ * (P.f (R.y (j + 1)) + P.h (R.y (j + 1))) ≤
      τ * (P.f (R.y j) + P.h (R.y j)) := mul_le_mul_of_nonneg_left hy1 hτ0.le
  have hE : (1 - τ) * (P.f (R.y (j + 1)) + P.h (R.y (j + 1))) ≤
      (1 - τ) * (P.f (R.x (j + 1)) + P.h (R.x (j + 1))) := mul_le_mul_of_nonneg_left hy2 h1τ
  rw [htj1, htj]
  linarith
