-- Prove2me | solution 1 for RobustMeanCov.OnePoint.twoPointValue_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:59:58.174182+00:00
-- url     : https://prove2.me/submissions/a52ec4a2-96a3-475c-8f4d-6829eeae2c82

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem aux_tpvd_sqrtA (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q : ℝ => Real.sqrt ((1 - q) / q))
      ((-1 / p ^ 2) / (2 * Real.sqrt ((1 - p) / p))) p := by
  have h1p : 0 < 1 - p := by linarith
  have h : HasDerivAt (fun q : ℝ => (1 - q) / q) (-1 / p ^ 2) p :=
    (((hasDerivAt_id' p).const_sub (1 : ℝ)).div (hasDerivAt_id' p) hp0.ne').congr_deriv
      (by ring)
  exact h.sqrt (div_pos h1p hp0).ne'

theorem aux_tpvd_sqrtB (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q : ℝ => Real.sqrt (q / (1 - q)))
      ((1 / (1 - p) ^ 2) / (2 * Real.sqrt (p / (1 - p)))) p := by
  have h1p : 0 < 1 - p := by linarith
  have h : HasDerivAt (fun q : ℝ => q / (1 - q)) (1 / (1 - p) ^ 2) p :=
    ((hasDerivAt_id' p).div ((hasDerivAt_id' p).const_sub (1 : ℝ)) h1p.ne').congr_deriv
      (by ring)
  exact h.sqrt (div_pos hp0 h1p).ne'

theorem aux_tpvd_identities (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    p * ((-1 / p ^ 2) / (2 * Real.sqrt ((1 - p) / p)))
        = -(Real.sqrt ((1 - p) / p) + Real.sqrt (p / (1 - p))) / 2 ∧
      (1 - p) * ((1 / (1 - p) ^ 2) / (2 * Real.sqrt (p / (1 - p))))
        = (Real.sqrt ((1 - p) / p) + Real.sqrt (p / (1 - p))) / 2 := by
  have h1p : 0 < 1 - p := by linarith
  have hApos : 0 < Real.sqrt ((1 - p) / p) := Real.sqrt_pos.mpr (div_pos h1p hp0)
  have hBpos : 0 < Real.sqrt (p / (1 - p)) := Real.sqrt_pos.mpr (div_pos hp0 h1p)
  have hA2 : Real.sqrt ((1 - p) / p) ^ 2 = (1 - p) / p := Real.sq_sqrt (div_pos h1p hp0).le
  have hB2 : Real.sqrt (p / (1 - p)) ^ 2 = p / (1 - p) := Real.sq_sqrt (div_pos hp0 h1p).le
  have hAB : Real.sqrt ((1 - p) / p) * Real.sqrt (p / (1 - p)) = 1 := by
    rw [← Real.sqrt_mul (div_pos h1p hp0).le]
    rw [show (1 - p) / p * (p / (1 - p)) = 1 by field_simp]
    simp
  generalize Real.sqrt ((1 - p) / p) = A at *
  generalize Real.sqrt (p / (1 - p)) = B at *
  have hpA2 : p * A ^ 2 = 1 - p := by rw [hA2]; field_simp
  have hqB2 : (1 - p) * B ^ 2 = p := by rw [hB2]; field_simp
  have h1 : p * A * (A + B) = 1 := by linear_combination hpA2 + p * hAB
  have h2 : (1 - p) * B * (A + B) = 1 := by linear_combination hqB2 + (1 - p) * hAB
  constructor
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination -h2

end RobustMeanCov.OnePoint

open RobustMeanCov.OnePoint

theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u) (m s p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => twoPointValue u m s q)
      (u (m + Real.sqrt ((1 - p) / p) * s) - u (m - Real.sqrt (p / (1 - p)) * s)
        - ((m + Real.sqrt ((1 - p) / p) * s) - (m - Real.sqrt (p / (1 - p)) * s))
          * (deriv u (m + Real.sqrt ((1 - p) / p) * s)
              + deriv u (m - Real.sqrt (p / (1 - p)) * s)) / 2) p := by
  obtain ⟨hp0, hp1⟩ := hp
  have hdA := aux_tpvd_sqrtA p hp0 hp1
  have hdB := aux_tpvd_sqrtB p hp0 hp1
  obtain ⟨hX, hY⟩ := aux_tpvd_identities p hp0 hp1
  have t1 := (hasDerivAt_id' p).mul ((hu _).hasDerivAt.comp p ((hdA.mul_const s).const_add m))
  have t2 := ((hasDerivAt_id' p).const_sub (1 : ℝ)).mul
    ((hu _).hasDerivAt.comp p ((hdB.mul_const s).const_sub m))
  have key := t1.add t2
  refine key.congr_deriv ?_
  simp only [Function.comp]
  linear_combination (s * deriv u (m + Real.sqrt ((1 - p) / p) * s)) * hX
    - (s * deriv u (m - Real.sqrt (p / (1 - p)) * s)) * hY
