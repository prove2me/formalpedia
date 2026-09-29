-- Prove2me | solution 1 for Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:11:54.56031+00:00
-- url     : https://prove2.me/submissions/9ba354c9-521b-448c-84fb-31a1af1ebb39

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
import Theorems.Thm_Mertens_E1Lambda_ge
import Theorems.Thm_Mertens_E1Lambda_le
import Theorems.Thm_Zeta23_Cheb_defect_bounded_explicit

-- from Zeta23.FromPNTPlus.Mertens
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 10e1218932db7e2432aa5881d750acb819e91f19, file
PrimeNumberTheoremAnd/Mertens.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Original authors per that project's blueprint (Euler–Maclaurin and Mertens
sections drawn from Leo Goldmakher, "A quick proof of Mertens' theorem",
https://web.williams.edu/Mathematics/lg5/mertens.pdf).

Declarations ported (source lines 1–371):
  Mertens.sum_Ioc_one_eq_sum_Ioc_zero, Mertens.sum_log_eq, Mertens.sum_log_le,
  Mertens.integral_log_le, Mertens.sum_log_ge, Mertens.sum_log_eq_log_factorial,
  Mertens.sum_log_eq_sum_mangoldt, Mertens.E₁Λ, Mertens.sum_mangoldt_div_eq,
  Mertens.E1Lambda.ge, Mertens.E1Lambda.le, Mertens.sum_mangoldt_div_eq_log,
  Mertens.E₁Λ.bounded'.

Local modifications:
  * the source's `section EulerMaclaurin` (B1 ... sum_eq_integral_add_integral_deriv)
    now lives in Zeta23/FromPNTPlus/EulerMaclaurin.lean (re-ported from upstream
    v4.32.2, where that section was split out of Mertens.lean into its own file),
    imported here;
  * dropped `import Architect` and all `@[blueprint ...]` attributes and
    `blueprint_comment` blocks (blueprint tooling we do not vendor); statement
    text retained as plain docstrings on the main theorems;
  * dropped three root-level helpers unused by the ported region (each is
    referenced only past our truncation point): Filter.EventuallyEq.iff_eventually,
    Real.inv_log_eq_o_one, Real.one_eq_o_log_log — nothing is injected into the
    Real or Filter namespaces by this file;
  * dropped a stray `#check ArithmeticFunction.vonMangoldt_sum`;
  * truncated after E₁Λ.bounded' (everything later — the sorry'd E₁Λ.bounded,
    the prime-form/second/third theorems — is not ported; no sorry enters);
  * added the closing `end Mertens`.
Modified 2026 by Anthropic PBC.
-/




namespace Mertens


open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log















/-- Mertens' first theorem (von Mangoldt form): for `x ≥ 1`, `|∑ d ≤ x, Λ(d)/d - log x| ≤ log 4 + 4`. -/
theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E1Lambda.le hx, E1Lambda.ge hx, log_nonneg]


end Mertens
end

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

/-- Mertens' first theorem (von Mangoldt form): |Σ_{n≤x} Λ(n)/n − log x| ≤ log 4 + 4
for x ≥ 1.  Paper [lem:cheb] cites it as "Mertens' formula"; classical [MV07 §2.2]. -/
theorem mertensFirst {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ Real.log 4 + 4 :=
  Mertens.sum_mangoldt_div_eq_log hx

/-- Partial sums of Λ(n)/n, in the Icc form produced by Abel summation. -/
noncomputable def Msum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k / k


lemma Msum_eq_Ioc (t : ℝ) : Msum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊


lemma Msum_mono : Monotone Msum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)


lemma Msum_nonneg (t : ℝ) : 0 ≤ Msum t :=
  Finset.sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)


/-- Abel summation with f = log, c n = Λ n / n. -/
lemma abel_log_Msum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
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

/-- Partial summation step: Σ_{n≤x} log n · Λ(n)/n = (log x)²/2 + O(log x). -/
lemma sum_log_mul_vonMangoldt_div_bound {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)) - Real.log x ^ 2 / 2|
      ≤ 2 * (Real.log 4 + 4) * Real.log x := by
  set K : ℝ := Real.log 4 + 4 with hK
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hMert : ∀ t : ℝ, 1 ≤ t → |Msum t - Real.log t| ≤ K := fun t ht => by
    rw [Msum_eq_Ioc]
    exact mertensFirst ht
  have habel := abel_log_Msum hx
  have hint_log : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_M : IntegrableOn (fun t : ℝ => t⁻¹ * Msum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono Msum_mono Msum_nonneg hx
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_diff : IntegrableOn (fun t : ℝ => t⁻¹ * (Msum t - Real.log t)) (Set.Ioc 1 x) :=
    ((hint_M.sub hint_log).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t)
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by
    rw [← MeasureTheory.integral_add hint_log hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| ≤ K * Real.log x := by
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (Msum t - Real.log t)‖ ≤ K * t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t⁻¹),
        mul_comm K t⁻¹]
      exact mul_le_mul_of_nonneg_left (hMert t ht1) (by positivity)
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
        ≤ ∫ t in Set.Ioc 1 x, K * t⁻¹ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le (hint_inv.const_mul K) hb
      _ = K * ∫ t in Set.Ioc 1 x, t⁻¹ := MeasureTheory.integral_const_mul K _
      _ = K * Real.log x := by rw [integral_inv_Ioc hx]
  have hMx : |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ K := mertensFirst hx
  rw [habel, hsplit, integral_inv_mul_log hx]
  have harr : Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n)
        - (Real.log x ^ 2 / 2 + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t))
        - Real.log x ^ 2 / 2
      = Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by ring
  rw [harr]
  have h1 : |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)| ≤ Real.log x * K := by
    rw [abs_mul, abs_of_nonneg hlx]
    exact mul_le_mul_of_nonneg_left hMx hlx
  calc |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
      ≤ |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)|
        + |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| := abs_sub _ _
    _ ≤ Real.log x * K + K * Real.log x := add_le_add h1 hE
    _ = 2 * K * Real.log x := by ring

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
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2|
      ≤ (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x := by
  set CD : ℝ := 1537 with hCDdef
  have hCD : ∀ y : ℝ, ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (Real.log n - Λ n) / n ≤ CD := by
    intro y
    rw [hCDdef]
    exact defect_bounded_explicit y
  have hCD0 : (0:ℝ) < CD := by rw [hCDdef]; norm_num
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  intro x hx
  show _ ≤ (2 * (Real.log 4 + 4) + CD / Real.log 2) * Real.log x
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 := abs_le.mp (sum_log_mul_vonMangoldt_div_bound hx1)
  have hdiff : (∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n))
        - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hD0 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n :=
    Finset.sum_nonneg fun n _ =>
      div_nonneg (mul_nonneg vonMangoldt_nonneg (sub_nonneg.mpr vonMangoldt_le_log))
        (Nat.cast_nonneg n)
  have hDle := hCD x
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hCDlog : CD ≤ CD / Real.log 2 * Real.log x := by
    have hkey : CD / Real.log 2 * Real.log 2 = CD := div_mul_cancel₀ CD hlog2pos.ne'
    calc CD = CD / Real.log 2 * Real.log 2 := hkey.symm
      _ ≤ CD / Real.log 2 * Real.log x :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hnn : (0 : ℝ) ≤ CD / Real.log 2 * Real.log x :=
    mul_nonneg (by positivity) (Real.log_nonneg hx1)
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]
