-- Prove2me | solution 1 for TaoFivePrimes.theta_log4_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:53:49.728624+00:00
-- url     : https://prove2.me/submissions/788a4569-1d62-4732-98f8-67976a37e46e

import Mathlib
open MeasureTheory Filter Set
open scoped Topology

theorem solution (E : ℝ → ℝ) (x : ℝ)
    (hx : 1 < x)
    (hE : ∀ t : ℝ, x ≤ t → |E t| ≤ 100 * t / (Real.log t) ^ 4) :
    |∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)| ≤
      25 / (Real.log x) ^ 4 + 20 / (Real.log x) ^ 5 := by
  let g : ℝ → ℝ := fun t => -(25 / (Real.log t) ^ 4 + 20 / (Real.log t) ^ 5)
  let d : ℝ → ℝ := fun t => 100 * (Real.log t + 1) / (t * (Real.log t) ^ 6)
  have hd : ∀ t ∈ Ici x, HasDerivAt g (d t) t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_of_lt_of_le hx ht)
    have hl : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (lt_of_lt_of_le hx ht))
    have h4 := (hasDerivAt_const t (25 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 4) (pow_ne_zero 4 hl)
    have h5 := (hasDerivAt_const t (20 : ℝ)).div
      ((Real.hasDerivAt_log htpos.ne').pow 5) (pow_ne_zero 5 hl)
    convert (h4.add h5).neg using 1 <;> (try rfl) <;> (try dsimp [g, d]) <;>
      field_simp [htpos.ne', hl] <;> ring
  have hdpos : ∀ t ∈ Ioi x, 0 ≤ d t := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one (lt_trans hx ht)
    have hl : 0 < Real.log t := Real.log_pos (lt_trans hx ht)
    dsimp [d]
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hh := ((hi.pow 4).const_mul 25 |>.add ((hi.pow 5).const_mul 20)).neg
    simpa [g, div_eq_mul_inv, inv_pow] using hh
  have hdi : IntegrableOn d (Ioi x) := integrableOn_Ioi_deriv_of_nonneg' hd hdpos hlim
  have hval : (∫ t in Ioi x, d t) = 25 / (Real.log x)^4 + 20 / (Real.log x)^5 := by
    simpa [g] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hdpos hlim
  rw [← hval]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hdi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := lt_trans zero_lt_one (lt_trans hx ht)
  have hl : 0 < Real.log t := Real.log_pos (lt_trans hx ht)
  have hbound := hE t (le_of_lt ht)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : 0 < Real.log t + 1),
    abs_of_pos (by positivity : 0 < t ^ 2 * Real.log t ^ 2)]
  calc
    |E t| * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) ≤
        (100 * t / Real.log t ^ 4) * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (by positivity)) (by positivity)
    _ = d t := by dsimp [d]; field_simp [htpos.ne', hl.ne'] <;> ring
