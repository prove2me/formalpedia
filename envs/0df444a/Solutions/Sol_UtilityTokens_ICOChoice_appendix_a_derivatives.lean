-- Prove2me | solution 1 for UtilityTokens.ICOChoice.appendix_a_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:40:42.35351+00:00
-- url     : https://prove2.me/submissions/157903e4-6072-47e7-bf3d-f0074edb9664

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

open UtilityTokens.ICOChoice in
theorem solution (Θ : ℝ) (hΘ : 0 < Θ) :
    let d := 2 / 3 * (1 - (2 * Θ + 1) / (4 * Real.sqrt (Θ ^ 2 + Θ + 1)))
    HasDerivAt thetaInterior d Θ ∧ 0 < d ∧
    thetaInterior Θ / Θ - d =
      2 / 3 + (1 - Real.sqrt (Θ ^ 2 + Θ + 1)) / (3 * Θ) - d ∧
    0 < thetaInterior Θ / Θ - d := by
  intro d
  have hq : (0:ℝ) < Θ ^ 2 + Θ + 1 := by positivity
  set s := Real.sqrt (Θ ^ 2 + Θ + 1) with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s ^ 2 = Θ ^ 2 + Θ + 1 := Real.sq_sqrt hq.le
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * Θ) Θ := by
    simpa using hasDerivAt_pow 2 Θ
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + t + 1) (2 * Θ + 1) Θ :=
    (hp.add (hasDerivAt_id' (x := Θ))).add_const 1
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + t + 1))
      ((2 * Θ + 1) / (2 * Real.sqrt (Θ ^ 2 + Θ + 1))) Θ := h1.sqrt (ne_of_gt hq)
  have h3 : HasDerivAt (fun t : ℝ => (2 * t + 1 - Real.sqrt (t ^ 2 + t + 1)) / 3)
      ((2 * 1 - (2 * Θ + 1) / (2 * Real.sqrt (Θ ^ 2 + Θ + 1))) / 3) Θ :=
    ((((hasDerivAt_id' (x := Θ)).const_mul (2:ℝ)).add_const (1:ℝ)).sub h2).div_const 3
  have heq : thetaInterior Θ / Θ =
      2 / 3 + (1 - s) / (3 * Θ) := by
    unfold thetaInterior
    rw [← hs_def]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · show HasDerivAt (fun t : ℝ => (2 * t + 1 - Real.sqrt (t ^ 2 + t + 1)) / 3) d Θ
    convert h3 using 1
    simp only [d]
    field_simp
    ring
  · have : (2 * Θ + 1) / 4 < s := by
      rw [hs_def]
      apply (Real.lt_sqrt (by positivity)).mpr
      nlinarith
    have h4 : (2 * Θ + 1) / (4 * s) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    simp only [d]
    linarith
  · rw [heq]
  · rw [heq]
    have hk : (Θ + 2) / 2 < s := by
      rw [hs_def]
      apply (Real.lt_sqrt (by positivity)).mpr
      nlinarith
    have key : 2 / 3 + (1 - s) / (3 * Θ) - d = (2 * s - 2 * s ^ 2 + 2 * Θ ^ 2 + Θ) / (6 * Θ * s) := by
      simp only [d]
      rw [← hs_def]
      field_simp
      ring
    rw [key]
    apply div_pos _ (by positivity)
    nlinarith
