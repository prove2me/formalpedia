-- Prove2me | solution 1 for TauCeti.tendsto_integral_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:23:38.344926+00:00
-- url     : https://prove2.me/submissions/f3ccdef4-a2d7-4756-a061-d4959eead251

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on the half-line `u ≥ -log x` by `exp (-u (sigma - 1))` and normalizing by
`x ^ (1 - sigma)`, the reciprocal of the damping at the left endpoint, leaves the integral of
an integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on
the half-line uniformly in `sigma ∈ (1, 2]`, so dominated convergence applies.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_integral_exp_mul`: the normalized damped integral converges to the undamped
  one as `sigma` decreases to `1`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Filter MeasureTheory Set
open scoped Topology

variable {f : ℝ → ℂ} {x : ℝ}

/-- On the half-line `u ≥ -log x` the damping factor `exp (-u (sigma - 1))` stays below a bound
depending only on `x`, uniformly for `sigma ∈ (1, 2]`. -/
private lemma TauCeti.exp_neg_mul_sub_one_le {u sigma : ℝ} (hu : -_root_.Real.log x ≤ u) (h1 : 1 < sigma)
    (h2 : sigma ≤ 2) : _root_.Real.exp (-u * (sigma - 1)) ≤ _root_.Real.exp (_root_.Max.max 0 (_root_.Real.log x)) := by
  refine Real.exp_le_exp.mpr ?_
  have hu' : -u ≤ _root_.Real.log x := by linarith
  rcases _root_.le_or_gt (-u) 0 with h | h
  · have hle : -u * (sigma - 1) ≤ 0 := by nlinarith
    exact hle.trans (_root_.le_max_left _ _)
  · have hle : -u * (sigma - 1) ≤ -u := by nlinarith
    exact hle.trans (hu'.trans (_root_.le_max_right _ _))

/-- As `sigma` decreases to `1`, the normalized one-sided Laplace transform of a function
integrable on the half-line `u ≥ -log x` converges to its undamped integral. -/
theorem solution (hx : 0 < x) (hf : _root_.MeasureTheory.IntegrableOn f (_root_.Set.Ici (-_root_.Real.log x))) :
    _root_.Filter.Tendsto (fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ) *
        ∫ u in _root_.Set.Ici (-_root_.Real.log x), (_root_.Real.exp (-u * (sigma - 1)) : ℂ) * f u)
      (𝓝[>] 1) (𝓝 (∫ u in _root_.Set.Ici (-_root_.Real.log x), f u)) := by
  have hrpow : _root_.Filter.Tendsto (fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    have hcont : _root_.Continuous fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ) := by
      simp only [_root_.Real.rpow_def_of_pos hx]
      fun_prop
    simpa using (hcont.tendsto 1).mono_left _root_.nhdsWithin_le_nhds
  have hint : _root_.Filter.Tendsto (fun sigma : ℝ ↦ ∫ u in _root_.Set.Ici (-_root_.Real.log x),
      (_root_.Real.exp (-u * (sigma - 1)) : ℂ) * f u) (𝓝[>] 1)
      (𝓝 (∫ u in _root_.Set.Ici (-_root_.Real.log x), f u)) := by
    refine _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ _root_.Real.exp (_root_.Max.max 0 (_root_.Real.log x)) * ‖f u‖)
      (.of_forall fun sigma ↦ (_root_.Continuous.aestronglyMeasurable (by fun_prop)).mul hf.1) ?_
      (hf.norm.const_mul _) (.of_forall fun u ↦ ?_)
    · filter_upwards [_root_.Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with sigma hsigma
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem _root_.measurableSet_Ici] with u hu
      rw [_root_.norm_mul, _root_.Complex.norm_real, _root_.Real.norm_eq_abs, _root_.abs_of_pos (_root_.Real.exp_pos _)]
      exact _root_.mul_le_mul_of_nonneg_right (_root_.TauCeti.exp_neg_mul_sub_one_le hu hsigma.1 hsigma.2)
        (_root_.norm_nonneg _)
    · have hone : _root_.Filter.Tendsto (fun sigma : ℝ ↦ ((_root_.Real.exp (-u * (sigma - 1)) : ℝ) : ℂ)) (𝓝[>] 1)
          (𝓝 1) := by
        have hcont : _root_.Continuous fun sigma : ℝ ↦ ((_root_.Real.exp (-u * (sigma - 1)) : ℝ) : ℂ) := by
          fun_prop
        simpa using (hcont.tendsto 1).mono_left _root_.nhdsWithin_le_nhds
      simpa using hone.mul_const (f u)
  simpa using hrpow.mul hint

end TauCeti

end
end
