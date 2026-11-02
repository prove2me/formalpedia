-- Prove2me | solution 1 for ServTimeLimit.OptMech.lambda1_foc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:17:00.892985+00:00
-- url     : https://prove2.me/submissions/f3b071d8-7bd0-4e02-8805-ffcc3ef24db9

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace STLLam1
open MeasureTheory ServTimeLimit.OptMech

/-- Closed form of the welfare of `[x, θ̄]` with `t(θ) = θ`. -/
noncomputable def G (l c b : ℝ) (x : ℝ) : ℝ :=
  l / b * ((b ^ 2 - x ^ 2) / 2 -
    (b - x) * (c * (l * ((b ^ 3 - x ^ 3) / 3) / (2 * (b - l * ((b ^ 2 - x ^ 2) / 2))))))

lemma welfare_eq (P : Params) (x : ℝ) (hx : x ≤ P.θbar) :
    welfare P (Set.Icc x P.θbar) (fun θ => θ) = G P.Lam P.c P.θbar x := by
  have hL : load (Set.Icc x P.θbar) (fun θ => θ) = (P.θbar ^ 2 - x ^ 2) / 2 := by
    unfold load
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx, integral_id]
  have hM : moment2 (Set.Icc x P.θbar) (fun θ => θ) = (P.θbar ^ 3 - x ^ 3) / 3 := by
    unfold moment2
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx, integral_pow]
    norm_num
  unfold welfare
  rw [integral_sub (f := fun θ : ℝ => θ)
    (g := fun _ : ℝ => P.c * waitTime P (Set.Icc x P.θbar) (fun θ => θ))
    (continuous_id.integrableOn_Icc) (continuous_const.integrableOn_Icc),
    setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith), smul_eq_mul]
  have : (∫ θ in Set.Icc x P.θbar, θ) = (P.θbar ^ 2 - x ^ 2) / 2 := hL
  rw [this]
  unfold waitTime
  rw [hL, hM]
  unfold G
  ring

/-- The derivative of `G` at `b/4`. -/
lemma G_deriv (l c b : ℝ) (hb : 0 < b) (hD : b - l * ((b ^ 2 - (b / 4) ^ 2) / 2) ≠ 0) :
    HasDerivAt (G l c b)
      (-(l * b ^ 2 * ((225 + 234 * c) * (l * b) ^ 2 - (960 + 768 * c) * (l * b) + 1024)) /
        (4096 * (b - l * ((b ^ 2 - (b / 4) ^ 2) / 2)) ^ 2)) (b / 4) := by
  have h1 : HasDerivAt (fun x : ℝ => (b ^ 2 - x ^ 2) / 2) (-(b / 4)) (b / 4) := by
    exact (((hasDerivAt_pow 2 (b / 4)).const_sub (b ^ 2)).div_const 2).congr_deriv
      (by norm_num; ring)
  have h2 : HasDerivAt (fun x : ℝ => (b ^ 3 - x ^ 3) / 3) (-(b / 4) ^ 2) (b / 4) := by
    exact (((hasDerivAt_pow 3 (b / 4)).const_sub (b ^ 3)).div_const 3).congr_deriv
      (by norm_num; ring)
  have h3 : HasDerivAt (fun x : ℝ => 2 * (b - l * ((b ^ 2 - x ^ 2) / 2))) (2 * (l * (b / 4)))
      (b / 4) := by
    exact (((h1.const_mul l).const_sub b).const_mul 2).congr_deriv (by ring)
  have h4 : HasDerivAt (fun x : ℝ => b - x) (-1) (b / 4) := by
    simpa using (hasDerivAt_id (b / 4)).const_sub b
  have hD2 : 2 * (b - l * ((b ^ 2 - (b / 4) ^ 2) / 2)) ≠ 0 := mul_ne_zero two_ne_zero hD
  have h5 := ((h2.const_mul l).div h3 hD2).const_mul c
  have h6 := (h1.sub (h4.mul h5)).const_mul (l / b)
  unfold G
  refine h6.congr_deriv ?_
  simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
  have hE : 32 - 15 * (l * b) ≠ 0 := by
    intro h; apply hD; linear_combination (b / 32) * h
  rw [show b - l * ((b ^ 2 - (b / 4) ^ 2) / 2) = b * (32 - 15 * (l * b)) / 32 by ring]
  have hb' : b ≠ 0 := hb.ne'
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 32 - 15 * (l * b) := ⟨_, rfl⟩
  rw [← hEdef] at hE ⊢
  field_simp
  rw [hEdef]
  ring

/-- The quadratic and its admissible root. -/
lemma quad_iff (c u : ℝ) (hc : 0 < c) (hu : u < 32 / 15) :
    (225 + 234 * c) * u ^ 2 - (960 + 768 * c) * u + 1024 = 0 ↔
      u = 32 * (4 * c + 5 - Real.sqrt (2 * c * (8 * c + 7))) / (3 * (26 * c + 25)) := by
  set r := Real.sqrt (2 * c * (8 * c + 7)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * c * (8 * c + 7) := Real.sq_sqrt (by positivity)
  have hK : 0 < 3 * (26 * c + 25) := by positivity
  set u1 := 32 * (4 * c + 5 - r) / (3 * (26 * c + 25)) with hu1
  set u2 := 32 * (4 * c + 5 + r) / (3 * (26 * c + 25)) with hu2
  have e1 : (225 + 234 * c) * (u1 + u2) = 960 + 768 * c := by
    rw [hu1, hu2]; field_simp; ring
  have e3 : (4 * c + 5 - r) * (4 * c + 5 + r) = 26 * c + 25 := by
    linear_combination (-1 : ℝ) * hr2
  have e4 : u1 * u2 = 1024 * ((4 * c + 5 - r) * (4 * c + 5 + r)) / (3 * (26 * c + 25)) ^ 2 := by
    rw [hu1, hu2]; field_simp; ring
  have e2 : (225 + 234 * c) * (u1 * u2) = 1024 := by
    rw [e4, e3]; field_simp; ring
  have hfac : (225 + 234 * c) * u ^ 2 - (960 + 768 * c) * u + 1024
      = (225 + 234 * c) * (u - u1) * (u - u2) := by
    linear_combination u * e1 - e2
  have hu2gt : 32 / 15 < u2 := by
    rw [hu2, lt_div_iff₀ hK]
    have : 6 * c < 5 * r := by
      by_contra hcon
      push Not at hcon
      nlinarith
    nlinarith
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · linarith
    · linarith
  · intro h; rw [h]; ring

end STLLam1

open MeasureTheory ServTimeLimit.OptMech in
theorem solution (P : Params) (hP : P.Standing) (hstab : P.Lam < 32 / (15 * P.θbar)) :
    HasDerivAt (fun x : ℝ => welfare P (Set.Icc x P.θbar) (fun θ => θ)) 0 (P.θbar / 4) ↔
      P.Lam = lam1 P := by
  obtain ⟨hl, hc, hb⟩ := hP
  have hlb : P.Lam * P.θbar < 32 / 15 := by
    rw [lt_div_iff₀ (by positivity)] at hstab; linarith
  have hD : P.θbar - P.Lam * ((P.θbar ^ 2 - (P.θbar / 4) ^ 2) / 2) ≠ 0 := by
    have : P.θbar - P.Lam * ((P.θbar ^ 2 - (P.θbar / 4) ^ 2) / 2) = P.θbar * (1 - 15 / 32 * (P.Lam * P.θbar)) := by ring
    rw [this]; apply mul_ne_zero hb.ne'; linarith
  have hev : (fun x : ℝ => welfare P (Set.Icc x P.θbar) (fun θ => θ)) =ᶠ[nhds (P.θbar / 4)]
      STLLam1.G P.Lam P.c P.θbar := by
    filter_upwards [Iio_mem_nhds (show P.θbar / 4 < P.θbar by linarith)] with x hx
    exact STLLam1.welfare_eq P x (le_of_lt hx)
  have hd := STLLam1.G_deriv P.Lam P.c P.θbar hb hD
  rw [hev.hasDerivAt_iff]
  constructor
  · intro h
    have h0 := hd.unique h
    have hq : (225 + 234 * P.c) * (P.Lam * P.θbar) ^ 2 - (960 + 768 * P.c) * (P.Lam * P.θbar) + 1024 = 0 := by
      have hden : (4096 * (P.θbar - P.Lam * ((P.θbar ^ 2 - (P.θbar / 4) ^ 2) / 2)) ^ 2) ≠ 0 := by positivity
      rw [neg_div, neg_eq_zero, div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rcases mul_eq_zero.mp h0 with h0 | h0
        · exfalso; have : 0 < P.Lam * P.θbar ^ 2 := by positivity
          linarith
        · exact h0
      · exact absurd h0 hden
    have := (STLLam1.quad_iff P.c (P.Lam * P.θbar) hc hlb).mp hq
    unfold lam1
    rw [eq_div_iff (by positivity),
      show P.Lam * (3 * (26 * P.c + 25) * P.θbar) = (P.Lam * P.θbar) * (3 * (26 * P.c + 25)) by ring,
      this]
    field_simp
  · intro h
    have hq : (225 + 234 * P.c) * (P.Lam * P.θbar) ^ 2 - (960 + 768 * P.c) * (P.Lam * P.θbar) + 1024 = 0 := by
      apply (STLLam1.quad_iff P.c (P.Lam * P.θbar) hc hlb).mpr
      rw [h]; unfold lam1; field_simp
    rw [hq] at hd
    simpa using hd
