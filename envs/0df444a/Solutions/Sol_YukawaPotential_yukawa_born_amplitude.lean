-- Prove2me | solution 1 for YukawaPotential.yukawa_born_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T17:53:36.366393+00:00
-- url     : https://prove2.me/submissions/2ebccc5a-7519-4293-8f6b-335daaa546b6

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

lemma cac02010_key (a q : ℝ) (ha : 0 < a) :
    ∫ r in Set.Ioi (0:ℝ), Real.exp (-(a * r)) * Real.sin (q * r) = q / (a ^ 2 + q ^ 2) := by
  set c : ℂ := -(a : ℂ) + q * Complex.I with hcdef
  have hc : c.re < 0 := by simp [c]; linarith
  have h := integral_exp_mul_complex_Ioi hc 0
  have hint := integrableOn_exp_mul_complex_Ioi hc 0
  have h2 : ∫ r in Set.Ioi (0:ℝ), (Complex.exp (c * r)).im
      = (∫ r in Set.Ioi (0:ℝ), Complex.exp (c * r)).im := integral_im hint
  have h3 : ∀ r : ℝ, (Complex.exp (c * r)).im = Real.exp (-(a * r)) * Real.sin (q * r) := by
    intro r
    rw [Complex.exp_im]
    simp [c]
  simp_rw [h3] at h2
  rw [h2, h]
  have hne : (a : ℂ) ^ 2 + (q : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show a ^ 2 + q ^ 2 ≠ 0 by positivity)
  simp [c, Complex.div_im, Complex.normSq_apply]
  field_simp

open YukawaPotential in
theorem solution (μ ℏ g α m q : ℝ) (hα : 0 < α) (hm : 0 < m) (hq : 0 < q) :
    -2 * μ / (ℏ ^ 2 * q) * ∫ r in Set.Ioi (0 : ℝ), r * yukawaPotential g α m r * Real.sin (q * r) =
      2 * μ * g ^ 2 / (ℏ ^ 2 * ((α * m) ^ 2 + q ^ 2)) := by
  have hI : ∫ r in Set.Ioi (0 : ℝ), r * yukawaPotential g α m r * Real.sin (q * r)
      = ∫ r in Set.Ioi (0 : ℝ), (-g ^ 2) * (Real.exp (-((α * m) * r)) * Real.sin (q * r)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [yukawaPotential]
    field_simp
  rw [hI, integral_const_mul, cac02010_key (α * m) q (mul_pos hα hm)]
  have hq0 : q ≠ 0 := hq.ne'
  have hs : 0 < (α * m) ^ 2 + q ^ 2 := by positivity
  rcases eq_or_ne ℏ 0 with h0 | h0
  · subst h0; simp
  · field_simp
