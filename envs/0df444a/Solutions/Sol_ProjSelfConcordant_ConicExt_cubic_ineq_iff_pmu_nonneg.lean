-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.cubic_ineq_iff_pmu_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:14:38.864989+00:00
-- url     : https://prove2.me/submissions/f8fef4a1-c799-4d80-9ff1-338a9543d0c6

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt.CubicProof

lemma rpow_three_halves (d : ℝ) (hd : 0 ≤ d) :
    d ^ (3 / 2 : ℝ) = (Real.sqrt d) ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2) * (3 : ℕ) by norm_num, Real.rpow_mul hd,
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]

lemma normalized_gap (a b c ν s t : ℝ) (hs : 0 < s) (hsq : s ^ 2 = b - a ^ 2) :
    4 * ν * ((a + s * t) ^ 2 - 2 * (a + s * t) * a + b) ^ 3 -
      (-2 * (a + s * t) ^ 3 + 6 * (a + s * t) ^ 2 * a - 6 * (a + s * t) * b + c) ^ 2 =
    s ^ 6 * pmu ν ((c - 6 * b * a + 4 * a ^ 3) / s ^ 3) t := by
  have hb : b = a ^ 2 + s ^ 2 := by linarith
  have hq : (a + s * t) ^ 2 - 2 * (a + s * t) * a + b = s ^ 2 * (t ^ 2 + 1) := by
    rw [hb]
    ring
  have hc : -2 * (a + s * t) ^ 3 + 6 * (a + s * t) ^ 2 * a - 6 * (a + s * t) * b + c =
      s ^ 3 * ((c - 6 * b * a + 4 * a ^ 3) / s ^ 3 - 2 * t ^ 3 - 6 * t) := by
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ (pow_ne_zero _ hs.ne')]
    rw [hb]
    ring
  have hp (μ : ℝ) : 4 * ν * (t ^ 2 + 1) ^ 3 - (μ - 2 * t ^ 3 - 6 * t) ^ 2 = pmu ν μ t := by
    unfold pmu
    ring
  rw [hq, hc, ← hp]
  ring

lemma normalized_iff (a b c ν s t : ℝ) (hs : 0 < s) (hsq : s ^ 2 = b - a ^ 2) :
    ((-2 * (a + s * t) ^ 3 + 6 * (a + s * t) ^ 2 * a - 6 * (a + s * t) * b + c) ^ 2 ≤
      4 * ν * ((a + s * t) ^ 2 - 2 * (a + s * t) * a + b) ^ 3) ↔
      0 ≤ pmu ν ((c - 6 * b * a + 4 * a ^ 3) / s ^ 3) t := by
  rw [← sub_nonneg, normalized_gap a b c ν s t hs hsq]
  exact mul_nonneg_iff_of_pos_left (pow_pos hs _)

end ProjSelfConcordant.ConicExt.CubicProof

open ProjSelfConcordant.ConicExt

theorem solution (a b c ν : ℝ) (hc2 : 0 < b - a ^ 2) :
    (∀ α : ℝ, (-2 * α ^ 3 + 6 * α ^ 2 * a - 6 * α * b + c) ^ 2
        ≤ 4 * ν * (α ^ 2 - 2 * α * a + b) ^ 3) ↔
      ∀ t : ℝ, 0 ≤ pmu ν ((c - 6 * b * a + 4 * a ^ 3) / (b - a ^ 2) ^ (3 / 2 : ℝ)) t := by
  let s := Real.sqrt (b - a ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr hc2
  have hsq : s ^ 2 = b - a ^ 2 := Real.sq_sqrt hc2.le
  have hp : (b - a ^ 2) ^ (3 / 2 : ℝ) = s ^ 3 := CubicProof.rpow_three_halves _ hc2.le
  rw [hp]
  constructor
  · intro h t
    exact (CubicProof.normalized_iff a b c ν s t hs hsq).mp (h (a + s * t))
  · intro h α
    have hinv : a + s * ((α - a) / s) = α := by
      rw [mul_div_cancel₀ _ hs.ne']
      ring
    have ht := (CubicProof.normalized_iff a b c ν s ((α - a) / s) hs hsq).mpr (h _)
    simpa only [hinv] using ht
