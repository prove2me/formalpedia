-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyholePrimitivePaths_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-19T00:37:46.20326+00:00
-- url     : https://prove2.me/submissions/c6aae67f-fcf7-4d53-b172-987d1f4e3a48

import Mathlib
import Definitions.Def_keyholeUpperBank
import Definitions.Def_keyholeLowerBank
import Definitions.Def_keyholeInnerArc
import Definitions.Def_keyholeOuterArc

theorem solution
    (a₀ a₁ r R : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => keyholeUpperBank (a₀ + 4 * t * (a₁ - a₀))) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeLowerBank (a₁ + (4 * t - 2) * (a₀ - a₁))) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeOuterArc R (4 * t - 1)) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeInnerArc r (4 * t - 3)) := by
  unfold keyholeUpperBank keyholeLowerBank keyholeOuterArc keyholeInnerArc
  have hreal1 : ContDiff ℝ 1 (fun t : ℝ => a₀ + 4 * t * (a₁ - a₀)) := by fun_prop
  have hreal2 : ContDiff ℝ 1 (fun t : ℝ => a₁ + (4 * t - 2) * (a₀ - a₁)) := by fun_prop
  have hreal3 : ContDiff ℝ 1 (fun t : ℝ => 4 * t - 1) := by fun_prop
  have hreal4 : ContDiff ℝ 1 (fun t : ℝ => 4 * t - 3) := by fun_prop
  have hc1 : ContDiff ℝ 1 (fun t : ℝ => ((a₀ + 4 * t * (a₁ - a₀) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal1
  have hc2 : ContDiff ℝ 1 (fun t : ℝ => ((a₁ + (4 * t - 2) * (a₀ - a₁) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal2
  have hc3 : ContDiff ℝ 1 (fun t : ℝ => ((4 * t - 1 : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal3
  have hc4 : ContDiff ℝ 1 (fun t : ℝ => ((4 * t - 3 : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)).comp hreal4
  constructor
  · simpa [zero_mul, add_zero] using hc1
  constructor
  · simpa [zero_mul, sub_zero] using hc2
  constructor
  · have harg : ContDiff ℝ 1 (fun t : ℝ =>
        Complex.I * (((4 * t - 1 : ℝ) : ℂ) * (Real.pi : ℂ))) := by
      fun_prop
    have hexp : ContDiff ℝ 1 (fun t : ℝ =>
        Complex.exp (Complex.I * (((4 * t - 1 : ℝ) : ℂ) * (Real.pi : ℂ)))) := by
      exact Complex.contDiff_exp.comp harg
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (R : ℂ))).mul hexp)
  · have harg : ContDiff ℝ 1 (fun t : ℝ =>
        Complex.I * (((4 * t - 3 : ℝ) : ℂ) * (Real.pi : ℂ))) := by
      fun_prop
    have hexp : ContDiff ℝ 1 (fun t : ℝ =>
        Complex.exp (Complex.I * (((4 * t - 3 : ℝ) : ℂ) * (Real.pi : ℂ)))) := by
      exact Complex.contDiff_exp.comp harg
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (r : ℂ))).mul hexp)
