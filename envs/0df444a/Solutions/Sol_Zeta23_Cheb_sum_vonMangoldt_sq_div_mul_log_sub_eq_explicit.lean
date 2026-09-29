-- Prove2me | solution 1 for Zeta23.Cheb.sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:10:39.36609+00:00
-- url     : https://prove2.me/submissions/47c4b6b1-6620-40b3-a99e-41fc8ae4ba49

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_eq_explicit

-- from Zeta23.Chebyshev
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Chebyshev.lean — discharge of the Chebyshev-type hypothesis H-cheb.

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line", Lemma [lem:cheb], displays [eq:cheb1]–[eq:cheb2]:

  "For x ≥ 2,
     Σ_{n≤x} Λ(n) ≪ x,   Σ_{n≤x} Λ(n)/√n ≤ 3√x  (x ≥ x₀),
     Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,   Σ_{n≤x} Λ(n)² ≪ x log x,    [eq:cheb1]
     Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),
     Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).       [eq:cheb2]"

H-cheb is classical [MV07 §2.2].  All sums here run over n ∈ Finset.Ioc 0 ⌊x⌋₊,
matching Mathlib's `Chebyshev.psi`.  The ≪-bounds are stated with explicit
existential constants; the paper's "≤ 3√x eventually" is provided in the robust
∃-constant form (the constant is not load-bearing downstream — [eq:Bdef] only
needs *some* B = l + C√X).

The two [eq:cheb2] asymptotics need Mertens' first theorem
Σ_{n≤x} Λ(n)/n = log x + O(1), which is not in Mathlib; it is supplied by
`mertensFirst` below, via Zeta23/FromPNTPlus/Mertens.lean.

Everything else comes from Mathlib (NumberTheory.Chebyshev ψ-bounds +
elementary induction/splitting arguments).
-/

namespace Zeta23
namespace Cheb

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-! ## [eq:cheb1], first bound: Σ_{n≤x} Λ(n) ≪ x -/


/-! ## [eq:cheb1], second bound: Σ_{n≤x} Λ(n)/√n ≪ √x -/


section Cheb1b

open MeasureTheory intervalIntegral

lemma sum_Icc_eq_sum_Ioc {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, c k = ∑ k ∈ Ioc 0 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc, zero_add]




end Cheb1b





/-! ## [eq:cheb1], third bound: Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x -/



/-! ## [eq:cheb1], fourth bound: Σ_{n≤x} Λ(n)² ≪ x log x -/



/-! ## [eq:cheb2]: the two Mertens-type asymptotics

Mertens' first theorem Σ_{n≤x} Λ(n)/n = log x + O(1) is supplied by
`Mertens.sum_mangoldt_div_eq_log` (see
Zeta23/FromPNTPlus/Mertens.lean), so both [eq:cheb2] bounds are unconditional. -/

section Cheb2

open MeasureTheory



/-- Partial sums of Λ(n)²/n, in the Icc form produced by Abel summation. -/
noncomputable def M2sum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k ^ 2 / k


lemma M2sum_eq_Ioc (t : ℝ) : M2sum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k ^ 2 / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊


lemma M2sum_mono : Monotone M2sum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)


lemma M2sum_nonneg (t : ℝ) : 0 ≤ M2sum t :=
  Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)


/-- Abel summation with f = log, c n = Λ n ^ 2 / n. -/
lemma abel_log_M2sum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n ^ 2 / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n ^ 2 / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n ^ 2 / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  rw [hL, hR] at habel
  rw [habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [Real.deriv_log]
  rfl

lemma integral_inv_Ioc {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
  rw [← intervalIntegral.integral_of_le hx, integral_inv ?h]
  · rw [div_one]
  case h =>
    rw [Set.uIcc_of_le hx]
    intro h
    rw [Set.mem_Icc] at h
    linarith [h.1]

lemma integral_inv_mul_log {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t = Real.log x ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (t⁻¹ * Real.log t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
    have heq : t⁻¹ * Real.log t = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

lemma integral_inv_mul_log_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t ^ 2 = Real.log x ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
    (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 3 / 3) (t⁻¹ * Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 3).div_const 3
    have heq : t⁻¹ * Real.log t ^ 2 = ((3 : ℕ) : ℝ) * Real.log t ^ (3 - 1) * t⁻¹ / 3 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t ^ 2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ (hlogcont.pow 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

/-- Integrability of t⁻¹·M on (1, x] for a monotone nonnegative M. -/
lemma integrableOn_inv_mul_mono {M : ℝ → ℝ} (hmono : Monotone M)
    (hnn : ∀ t, 0 ≤ M t) {x : ℝ} (_hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * M t) (Set.Ioc 1 x) := by
  refine Integrable.mono' (g := fun _ => M x)
    (integrableOn_const (by simp)) ?_ ?_
  · exact (measurable_inv.mul hmono.measurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hti : t⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; linarith
    have h0 : (0 : ℝ) ≤ t⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hnn t))]
    calc t⁻¹ * M t ≤ 1 * M t := mul_le_mul_of_nonneg_right hti (hnn t)
      _ = M t := one_mul _
      _ ≤ M x := hmono ht.2


/-! ### The proper-prime-power defect

[lem:cheb] proof: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) (the two differ
only at proper prime powers)".  The defect Σ_{n≤x} Λ(n)(log n − Λ(n))/n is
supported on prime powers pᵏ with k ≥ 2, where its value is (k−1)log²p/pᵏ;
summing over all p, k bounds it by an absolute constant. -/















end Cheb2

end Cheb
end Zeta23
open Zeta23
open Cheb
open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime
open MeasureTheory

theorem solution : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
        Real.log x ^ 3 / 6|
      ≤ ((2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
  set C2 : ℝ := 2 * (Real.log 4 + 4) + 1537 / Real.log 2 with hC2def
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hC2 : ∀ y : ℝ, 2 ≤ y → |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n ^ 2 / n) - Real.log y ^ 2 / 2|
      ≤ C2 * Real.log y := by
    intro y hy
    rw [hC2def]
    exact sum_vonMangoldt_sq_div_eq_explicit y hy
  have hC20 : (0:ℝ) < C2 := by
    rw [hC2def]
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  intro x hx
  show _ ≤ (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  -- the target sum equals ∫ t⁻¹ M2sum t
  have habel := abel_log_M2sum hx1
  have hident : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
      = ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
    have e1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
        = Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n)
          - ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e1, habel]
    ring
  rw [hident]
  -- pointwise bound for the error density on (1, x]
  have hM2b : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      |M2sum t - Real.log t ^ 2 / 2| ≤ C2 * Real.log t + 1 := by
    intro t ht
    have hlt0 : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht.1.le
    rcases le_or_gt 2 t with h2 | h2
    · have h := hC2 t h2
      rw [M2sum_eq_Ioc]
      have hC2log : (0 : ℝ) ≤ C2 * Real.log t := mul_nonneg hC20.le hlt0
      calc |(∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n ^ 2 / n) - Real.log t ^ 2 / 2| ≤ C2 * Real.log t := h
        _ ≤ C2 * Real.log t + 1 := by linarith
    · have ht1 : (1 : ℝ) < t := ht.1
      have hfl : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ t)]
        constructor
        · exact_mod_cast ht1.le
        · exact_mod_cast (by linarith : t < 1 + 1)
      have hM20 : M2sum t = 0 := by
        rw [M2sum_eq_Ioc, hfl]
        rw [show Finset.Ioc 0 1 = {1} from rfl]
        simp [vonMangoldt_apply_one]
      rw [hM20, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hlt2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) h2.le
      have hl21 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
      nlinarith [mul_nonneg hC20.le hlt0]
  -- integrabilities
  have hcont_logsq : IntegrableOn (fun t : ℝ => t⁻¹ * (Real.log t ^ 2 / 2)) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
      (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    refine ContinuousOn.mul ?_ ((hlogcont.pow 2).div_const 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_M2 : IntegrableOn (fun t : ℝ => t⁻¹ * M2sum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono M2sum_mono M2sum_nonneg hx1
  have hint_diff : IntegrableOn
      (fun t : ℝ => t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)) (Set.Ioc 1 x) :=
    ((hint_M2.sub hcont_logsq).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2))
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by
    rw [← MeasureTheory.integral_add hcont_logsq hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hval : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2) = Real.log x ^ 3 / 6 := by
    have e : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2)
        = ∫ t in Set.Ioc 1 x, (t⁻¹ * Real.log t ^ 2) * (1 / 2) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
    rw [e, MeasureTheory.integral_mul_const, integral_inv_mul_log_sq hx1]
    ring
  -- error bound
  have hint_invlog : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := by
    have hg_int : IntegrableOn (fun t : ℝ => C2 * (t⁻¹ * Real.log t) + t⁻¹) (Set.Ioc 1 x) :=
      (hint_invlog.const_mul C2).add hint_inv
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)‖ ≤ C2 * (t⁻¹ * Real.log t) + t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have hti : (0 : ℝ) ≤ t⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hti]
      calc t⁻¹ * |M2sum t - Real.log t ^ 2 / 2| ≤ t⁻¹ * (C2 * Real.log t + 1) :=
            mul_le_mul_of_nonneg_left (hM2b t ht) hti
        _ = C2 * (t⁻¹ * Real.log t) + t⁻¹ := by ring
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
        ≤ ∫ t in Set.Ioc 1 x, (C2 * (t⁻¹ * Real.log t) + t⁻¹) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le hg_int hb
      _ = C2 * (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t) + ∫ t in Set.Ioc 1 x, t⁻¹ := by
          rw [MeasureTheory.integral_add (hint_invlog.const_mul C2) hint_inv,
            MeasureTheory.integral_const_mul]
      _ = C2 * (Real.log x ^ 2 / 2) + Real.log x := by
          rw [integral_inv_mul_log hx1, integral_inv_Ioc hx1]
  -- assemble
  rw [hsplit, hval]
  have harr : Real.log x ^ 3 / 6
        + (∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2))
        - Real.log x ^ 3 / 6
      = ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by ring
  rw [harr]
  have hlogx2 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    nlinarith [hlx]
  calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := hE
    _ ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x ^ 2 / Real.log 2 := by linarith
    _ = (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
        field_simp
