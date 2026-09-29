-- Prove2me | solution 1 for RobustMeanCov.OnePoint.quadratic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:17:06.152603+00:00
-- url     : https://prove2.me/submissions/edc3460b-7ae8-4a09-81b7-d7ab3e5324cb

import Mathlib
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory

namespace RobustMeanCov.OnePoint

theorem aux_qlb_second_moment (m s : ℝ) (ν : Measure ℝ)
    (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2)) :
    IsProbabilityMeasure ν ∧ Integrable (fun y : ℝ => y) ν ∧
      Integrable (fun y : ℝ => y ^ 2) ν ∧ ∫ y, y ∂ν = m ∧ ∫ y, y ^ 2 ∂ν = m ^ 2 + s ^ 2 := by
  obtain ⟨hprob, hmem, hmean, hvar⟩ := hν
  have hi1 : Integrable (fun y : ℝ => y) ν := hmem.integrable (by norm_num)
  have hi2 : Integrable (fun y : ℝ => y ^ 2) ν := hmem.integrable_sq
  refine ⟨hprob, hi1, hi2, hmean, ?_⟩
  have hexp : (fun r : ℝ => (r - m) ^ 2) = fun r => (r ^ 2 + (-2 * m) * r) + m ^ 2 := by
    funext r; ring
  have hi3 : Integrable (fun r : ℝ => r ^ 2 + (-2 * m) * r) ν := hi2.add (hi1.const_mul _)
  have hi4 : Integrable (fun r : ℝ => (-2 * m) * r) ν := hi1.const_mul _
  rw [hexp, integral_add hi3 (integrable_const _),
    integral_add hi2 hi4, integral_const_mul, integral_const, hmean] at hvar
  simp at hvar
  linarith

end RobustMeanCov.OnePoint

open RobustMeanCov.OnePoint
open MeasureTheory

theorem solution (u : ℝ → ℝ) (m s : ℝ) (ν : Measure ℝ)
    (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2)) (hint : Integrable u ν) (A B C : ℝ)
    (hq : ∀ y : ℝ, A * y ^ 2 + B * y + C ≤ u y) :
    A * (m ^ 2 + s ^ 2) + B * m + C ≤ ∫ y, u y ∂ν := by
  obtain ⟨hprob, hi1, hi2, hmean, hsq⟩ := aux_qlb_second_moment m s ν hν
  have hA : Integrable (fun y : ℝ => A * y ^ 2) ν := hi2.const_mul A
  have hB : Integrable (fun y : ℝ => B * y) ν := hi1.const_mul B
  have hAB : Integrable (fun y : ℝ => A * y ^ 2 + B * y) ν := hA.add hB
  have hq_int : Integrable (fun y : ℝ => A * y ^ 2 + B * y + C) ν :=
    hAB.add (integrable_const C)
  have hmono : ∫ y, (A * y ^ 2 + B * y + C) ∂ν ≤ ∫ y, u y ∂ν :=
    integral_mono hq_int hint hq
  have hcalc : ∫ y, (A * y ^ 2 + B * y + C) ∂ν = A * (m ^ 2 + s ^ 2) + B * m + C := by
    rw [integral_add hAB (integrable_const C),
      integral_add hA hB, integral_const_mul, integral_const_mul,
      integral_const, hsq, hmean]
    simp
  linarith
