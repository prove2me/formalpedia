-- Prove2me | solution 1 for TauCeti.LSeries.tendsto_integral_vertical
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:19.857173+00:00
-- url     : https://prove2.me/submissions/553fd2d3-3bd9-4c4e-91f2-5e64554e13fe

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The limiting Fourier identity for Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` tests a Dirichlet series against an
integrable function on a vertical line `Re s = sigma` strictly inside the half-plane of
convergence. This file lets `sigma` decrease to `1` and records the resulting identity on the
boundary line itself.

Each of the three terms of that identity has its own limit argument, and each is stated separately
so that a later step can reuse it: the Dirichlet series converges by the uniform convergence of a
summable Dirichlet series on a closed half-plane, while the two integrals converge by dominated
convergence, the pole term because the exponential damping `exp (-u (sigma - 1))` is bounded on
the half-line of integration, and the vertical integral because a test function with compact
support confines the integrand to a compact box on which `G` is continuous.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane
`Re s ≥ 1`; nothing is assumed about `LSeries a` there, where it is a total function with junk
values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier` and
  `TauCeti.LSeries.tendsto_integral_vertical` are two of the three one-sided limits; the third,
  for the pole term, is the general `TauCeti.tendsto_integral_exp_mul`.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` is the identity they
  combine into, and
  `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` is its form
  for a smooth test function, where the half-line integrability hypothesis is automatic by
  `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`.

## Provenance

The decomposition into three separate one-sided limits, and the shape of the identity they
combine into, follow `limiting_fourier_lim1`, `limiting_fourier_lim2`, `limiting_fourier_lim3`
and `limiting_fourier` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling file
`TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier`. The proofs here are written against
Mathlib's uniform- and dominated-convergence lemmas, and the hypotheses differ: the Chebyshev-type
bound of the source is replaced by the summability of the Fourier-weighted series at `s = 1`,
which is what the limit actually consumes.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ} {x : ℝ}

/-! ### The Dirichlet series -/



/-! ### The integral along the vertical line -/

/-- As `sigma` decreases to `1`, the integral of `G` along the vertical line `Re s = sigma`
against a compactly supported test function converges to the same integral along the boundary
line, because the integrand is confined to a compact box on which `G` is continuous. -/
theorem solution (hx : 0 < x) (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hpsi : _root_.MeasureTheory.Integrable psi) (hsupp : _root_.HasCompactSupport psi) :
    _root_.Filter.Tendsto (fun sigma : ℝ ↦ ∫ t : ℝ, G (sigma + t * _root_.Complex.I) * psi t * (x : ℂ) ^ (t * _root_.Complex.I))
      (𝓝[>] 1) (𝓝 (∫ t : ℝ, G (1 + t * _root_.Complex.I) * psi t * (x : ℂ) ^ (t * _root_.Complex.I))) := by
  have hmem {sigma : ℝ} (hsigma : 1 ≤ sigma) (t : ℝ) :
      (sigma : ℂ) + t * _root_.Complex.I ∈ {z : ℂ | 1 ≤ z.re} := by simpa using hsigma
  have hcompact : _root_.IsCompact ((fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * _root_.Complex.I) '' (_root_.Set.Icc 1 2 ×ˢ _root_.tsupport psi)) :=
    (isCompact_Icc.prod hsupp).image (by fun_prop)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn <| hG.mono <| by
    rintro _ ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩
    exact hmem hs.1 t
  have hxnorm (t : ℝ) : ‖(x : ℂ) ^ (t * _root_.Complex.I)‖ = 1 := by
    rw [_root_.Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hxpow : _root_.Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * _root_.Complex.I) :=
    continuous_const.cpow (continuous_ofReal.mul _root_.continuous_const) (by simp [hx])
  refine _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun t ↦ C * ‖psi t‖) ?_ ?_
    (hpsi.norm.const_mul C) (.of_forall fun t ↦ ?_)
  · filter_upwards [_root_.self_mem_nhdsWithin] with sigma hsigma
    exact ((hG.comp_continuous (by fun_prop) (hmem (_root_.le_of_lt hsigma))).aestronglyMeasurable.mul
      hpsi.aestronglyMeasurable).mul hxpow.aestronglyMeasurable
  · filter_upwards [_root_.Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with sigma hsigma
    filter_upwards with t
    by_cases ht : psi t = 0
    · simp [ht]
    · have hmemK : (sigma : ℂ) + t * _root_.Complex.I ∈
          (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * _root_.Complex.I) '' (_root_.Set.Icc 1 2 ×ˢ _root_.tsupport psi) :=
        ⟨(sigma, t), ⟨⟨hsigma.1.le, hsigma.2⟩, _root_.subset_tsupport _ ht⟩, _root_.rfl⟩
      calc ‖G (sigma + t * _root_.Complex.I) * psi t * (x : ℂ) ^ (t * _root_.Complex.I)‖
          = ‖G (sigma + t * _root_.Complex.I)‖ * ‖psi t‖ := by
            rw [_root_.norm_mul, _root_.norm_mul, hxnorm t, _root_.mul_one]
        _ ≤ C * ‖psi t‖ := _root_.mul_le_mul_of_nonneg_right (hC _ hmemK) (_root_.norm_nonneg _)
  · have hmem1 : (1 : ℂ) + t * _root_.Complex.I ∈ {z : ℂ | 1 ≤ z.re} := by simp
    refine _root_.Filter.Tendsto.mul_const _ (_root_.Filter.Tendsto.mul_const _ ?_)
    refine _root_.Filter.Tendsto.comp (hG.continuousWithinAt hmem1) ?_
    refine _root_.tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun sigma : ℝ ↦ (sigma : ℂ) + t * I).tendsto' 1 _
        (by simp)).mono_left _root_.nhdsWithin_le_nhds) ?_
    filter_upwards [_root_.self_mem_nhdsWithin] with sigma hsigma
    exact hmem (_root_.le_of_lt hsigma) t

/-! ### The identity on the boundary line -/





end TauCeti.LSeries

end
end
