-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.intg_pow_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:13.206055+00:00
-- url     : https://prove2.me/submissions/f583f17c-ee1a-4566-b6b5-fdde7ea30c02

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (k : ℕ) (c : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
  have h1 := (integrable_cexp_quadratic' hb (c + 1) 0).norm
  have h2 := (integrable_cexp_quadratic' hb (c - 1) 0).norm
  refine Integrable.mono' ((h1.add h2).const_mul (k.factorial : ℝ)) ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine Filter.Eventually.of_forall fun x => ?_
    have hk : |x| ^ k ≤ k.factorial * Real.exp |x| := by
      have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)] at this
      linarith
    have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
      rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]
    set E := Real.exp ((b * (x : ℂ) ^ 2 + c * x).re) with hE
    have r1 : ‖cexp (b * (x : ℂ) ^ 2 + (c + 1) * x + 0)‖ = E * Real.exp x := by
      rw [Complex.norm_exp, hE, ← Real.exp_add]; congr 1; simp [add_mul]; try ring
    have r2 : ‖cexp (b * (x : ℂ) ^ 2 + (c - 1) * x + 0)‖ = E * Real.exp (-x) := by
      rw [Complex.norm_exp, hE, ← Real.exp_add]; congr 1; simp [sub_mul]; try ring
    have r0 : ‖(x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)‖ = |x| ^ k * E := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp only [Pi.add_apply]
    rw [r0, r1, r2]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc |x| ^ k * E ≤ (k.factorial * Real.exp |x|) * E := mul_le_mul_of_nonneg_right hk hE0
      _ ≤ (k.factorial * (Real.exp x + Real.exp (-x))) * E := by gcongr
      _ = k.factorial * (E * Real.exp x + E * Real.exp (-x)) := by ring
end PositivityTheory.SiegelWeilFormula.KLI
