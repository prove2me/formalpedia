-- Prove2me | solution 1 for YukawaPotential.yukawa_total_cross_section
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:53:36.381305+00:00
-- url     : https://prove2.me/submissions/6d37a767-87aa-46d8-ab27-d5e7a90d7541

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

lemma b6abf990_core (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    ∫ θ in (0 : ℝ)..Real.pi,
        (2 * Real.pi * Real.sin θ / (a + c * (1 - Real.cos θ)) ^ 2) =
      4 * Real.pi / (a * (a + 2 * c)) := by
  have hden : ∀ θ : ℝ, 0 < a + c * (1 - Real.cos θ) := by
    intro θ
    have h1 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    have := mul_nonneg hc h1
    linarith
  let F : ℝ → ℝ := fun θ => 2 * Real.pi * (1 - Real.cos θ) / (a * (a + c * (1 - Real.cos θ)))
  have hderiv : ∀ θ : ℝ,
      HasDerivAt F (2 * Real.pi * Real.sin θ / (a + c * (1 - Real.cos θ)) ^ 2) θ := by
    intro θ
    have hu : HasDerivAt (fun x => 1 - Real.cos x) (Real.sin θ) θ := by
      simpa using (Real.hasDerivAt_cos θ).const_sub 1
    have hnum : HasDerivAt (fun x => 2 * Real.pi * (1 - Real.cos x))
        (2 * Real.pi * Real.sin θ) θ := hu.const_mul (2 * Real.pi)
    have hd : HasDerivAt (fun x => a * (a + c * (1 - Real.cos x)))
        (a * (c * Real.sin θ)) θ := ((hu.const_mul c).const_add a).const_mul a
    have hne : a * (a + c * (1 - Real.cos θ)) ≠ 0 := (mul_pos ha (hden θ)).ne'
    have h2 := (hden θ).ne'
    have e : (2 * Real.pi * Real.sin θ * (a * (a + c * (1 - Real.cos θ))) -
        2 * Real.pi * (1 - Real.cos θ) * (a * (c * Real.sin θ))) /
          (a * (a + c * (1 - Real.cos θ))) ^ 2
        = 2 * Real.pi * Real.sin θ / (a + c * (1 - Real.cos θ)) ^ 2 := by
      rw [div_eq_div_iff (pow_ne_zero 2 hne) (pow_ne_zero 2 h2)]
      ring
    exact (hnum.div hd hne).congr_deriv e
  have hcont : Continuous (fun θ : ℝ =>
      2 * Real.pi * Real.sin θ / (a + c * (1 - Real.cos θ)) ^ 2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    exact pow_ne_zero 2 (hden θ).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (hcont.intervalIntegrable _ _)]
  simp only [F, Real.cos_pi, Real.cos_zero]
  have h3 : 0 < a + 2 * c := by linarith
  field_simp
  ring

theorem solution (μ ℏ g α m p : ℝ) (hα : 0 < α) (hm : 0 < m) :
    ∫ θ in (0 : ℝ)..Real.pi,
        4 * μ ^ 2 * g ^ 4 / ℏ ^ 4 *
          (2 * Real.pi * Real.sin θ / ((α * m) ^ 2 + 4 * p ^ 2 * Real.sin (θ / 2) ^ 2) ^ 2) =
      4 * μ ^ 2 * g ^ 4 / ℏ ^ 4 * (4 * Real.pi / ((α * m) ^ 2 * ((α * m) ^ 2 + 4 * p ^ 2))) := by
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have key : ∀ θ : ℝ, 2 * Real.pi * Real.sin θ / ((α * m) ^ 2 + 4 * p ^ 2 * Real.sin (θ / 2) ^ 2) ^ 2
      = 2 * Real.pi * Real.sin θ / ((α * m) ^ 2 + (2 * p ^ 2) * (1 - Real.cos θ)) ^ 2 := by
    intro θ
    have hc : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [hc, Real.cos_two_mul, Real.sin_sq]
    ring
  simp_rw [key]
  rw [b6abf990_core ((α * m) ^ 2) (2 * p ^ 2) (by positivity) (by positivity)]
  ring
