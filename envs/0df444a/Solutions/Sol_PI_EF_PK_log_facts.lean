-- Prove2me | solution 1 for PI.EF.PK.log_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:55.492565+00:00
-- url     : https://prove2.me/submissions/f3188f69-7c9e-402b-b167-24961387e36d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_log_le_two_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution {N : ℕ} {u T T' : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T')
    (hT'1 : T' ≤ T + 1) :
    0 ≤ Real.log (N * u * T) ∧ Real.log (N * T') ≤ Real.log (N * u * T) ∧
      0 ≤ Real.log (N * T') ∧ Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T) ∧
      Real.log (1 + 2 * (2 * T')) ≤ 2 * Real.log (N * u * T) ∧ 0 ≤ Real.log (N * (T' + 2)) ∧
      0 ≤ Real.log (N * u) := by
  have hT0 : 0 < T := by linarith
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hN0 : 0 < (N : ℝ) := by linarith
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hNu : 2 ≤ (N : ℝ) * u := by nlinarith
  have hNuT : 4 ≤ (N : ℝ) * u * T := by nlinarith
  have hY2 : (N : ℝ) * (4 * T ^ 2) ≤ ((N : ℝ) * u * T) ^ 2 := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * T ^ 2 ≤ u ^ 2 * T ^ 2 := by
      have hu4 : 4 ≤ u ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hu4 (sq_nonneg T)
    calc (N : ℝ) * (4 * T ^ 2) ≤ (N : ℝ) ^ 2 * (u ^ 2 * T ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((N : ℝ) * u * T) ^ 2 := by ring
  have hNT' : 1 ≤ (N : ℝ) * T' := by nlinarith
  have hNT'2 : 1 ≤ (N : ℝ) * (T' + 2) := by nlinarith
  refine ⟨Real.log_nonneg (by linarith), Real.log_le_log (by nlinarith) ?_, Real.log_nonneg hNT', ?_, ?_,
    Real.log_nonneg hNT'2, Real.log_nonneg (by linarith)⟩
  · have h : T' ≤ u * T := by nlinarith
    calc (N : ℝ) * T' ≤ N * (u * T) := mul_le_mul_of_nonneg_left h hN0.le
      _ = N * u * T := by ring
  · apply log_le_two_mul (by nlinarith)
    calc (N : ℝ) * (T' + 2) ≤ N * (4 * T ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hN0.le
      _ ≤ _ := hY2
  · apply log_le_two_mul (by nlinarith)
    calc 1 + 2 * (2 * T') ≤ (N : ℝ) * (4 * T ^ 2) := by nlinarith
      _ ≤ _ := hY2
end PI.EF.PK
