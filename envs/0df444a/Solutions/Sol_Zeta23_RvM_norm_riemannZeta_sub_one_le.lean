-- Prove2me | solution 1 for Zeta23.RvM.norm_riemannZeta_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:48:33.629972+00:00
-- url     : https://prove2.me/submissions/26e8413a-6dca-452b-a80d-96ac88fb90e0

import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds

-- from Zeta23.RvM.ZetaGrowth
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/


/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/






/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/









end RvM
end Zeta23
end
open Complex Set MeasureTheory Real

theorem solution {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  -- the shifted Dirichlet series  f n := 1/(n+1)^s,  ζ s = ∑' f n
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum : Summable f := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs1
    have := (summable_nat_add_iff 1).mpr h0
    simpa [f] using this
  have hzeta : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0 : f 0 = 1 := by simp [f]
  have hsplit : riemannZeta s - 1 = ∑' n, f (n + 1) := by
    rw [hzeta, hsum.tsum_eq_zero_add, hf0]; ring
  -- termwise comparison with 1/(n+2)^2
  have hle : ∀ n : ℕ, ‖f (n + 1)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hpos : 0 < n + 2 := by omega
    have hf1 : f (n + 1) = 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
      simp only [f]
      congr 2
      push_cast
      ring
    rw [hf1, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    calc 1 / ((n + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 :=
          one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((n : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  rw [hsplit]
  have hsum' : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq
