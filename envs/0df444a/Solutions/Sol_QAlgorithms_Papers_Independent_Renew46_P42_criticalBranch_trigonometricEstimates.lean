-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.criticalBranch_trigonometricEstimates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:37:41.704761+00:00
-- url     : https://prove2.me/submissions/f3e4a744-18c2-40e1-b0c6-b53609db185a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open Real
theorem g64h_arccos_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.arccos y ≤ (π / 2) * Real.sqrt (1 - y) := by
  set θ := Real.arccos y with hθ
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg y
  have hθ1 : θ ≤ π / 2 := Real.arccos_le_pi_div_two.2 h0
  have hcos : Real.cos θ = y := Real.cos_arccos (by linarith) h1
  have hpi := Real.pi_pos
  -- concavity
  have hconc := strictConcaveOn_sin_Icc.concaveOn
  have hb0 : 0 ≤ 2 * θ / π := by positivity
  have hb1 : 2 * θ / π ≤ 1 := by rw [div_le_one hpi]; linarith
  have key := hconc.2 (x := 0) (y := π / 4) ⟨le_refl 0, by positivity⟩ ⟨by positivity, by linarith⟩
    (sub_nonneg.2 hb1) hb0 (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, Real.sin_pi_div_four] at key
  have e : 2 * θ / π * (π / 4) = θ / 2 := by field_simp; ring
  rw [e] at key
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (2 * θ / π) ^ 2 ≤ 1 - y := by
    rw [← hcos]
    have : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at this; nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
    rw [this]
    have hp : 0 ≤ 2 * θ / π * (Real.sqrt 2 / 2) := by positivity
    have := pow_le_pow_left₀ hp key 2
    nlinarith
  have := Real.le_sqrt_of_sq_le hsq
  calc θ = (π / 2) * (2 * θ / π) := by field_simp
    _ ≤ (π / 2) * Real.sqrt (1 - y) := by gcongr

/-- PDF p.10, (97): the two auxiliary real trigonometric estimates, with
exactly the printed intervals and constants. -/
theorem solution :
    (∀ x : ℝ, -1 ≤ x → x ≤ 0 →
      Real.arccos x ≥ -(1 / 2 : ℝ) * Real.sqrt (1 + x) * Real.pi + Real.pi) ∧
    (∀ x : ℝ, Real.pi / 2 ≤ x → x ≤ Real.pi →
      Real.cos x ≥ (3 / Real.pi) * x - (9 / 2 : ℝ)) := by
  refine ⟨fun x h1 h0 => ?_, fun x h1 h2 => ?_⟩
  · have := g64h_arccos_le (-x) (by linarith) (by linarith)
    rw [Real.arccos_neg] at this
    rw [show 1 + x = 1 - -x by ring]
    nlinarith [Real.pi_pos]
  · have hp := Real.pi_pos
    have : 3 / Real.pi * x ≤ 3 := by rw [div_mul_eq_mul_div, div_le_iff₀ hp]; linarith
    linarith [Real.neg_one_le_cos x]


end

