-- Prove2me | solution 1 for TaoFivePrimes.ramare_squarefree_totient_sum_le_large
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:38:20.051592+00:00
-- url     : https://prove2.me/submissions/dc047b65-3c66-4d72-b288-472129c4b4a1

import Theorems.Thm_RamareAnalytic_exists_squarefree_totient_harmonic_coefficients
import Theorems.Thm_RamareAnalytic_moments_of_prime_power_values
import Theorems.Thm_RamareAnalytic_harmonic_convolution_error_le
import Theorems.Thm_RamareAnalytic_coefficient_logarithmic_moment
import Theorems.Thm_RamareAnalytic_global_logarithmic_constant_le
import Theorems.Thm_RamareAnalytic_weighted_moment_le_sixteen
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/- Draft parent adapter. The future weighted-moment import must exist before submission.
No full public-import local compilation is claimed by this generated artifact. -/

set_option autoImplicit false
open scoped BigOperators

namespace RamareAnalytic

/-!
Internal assembly interface for the existing large-range Ramaré target.
This file deliberately keeps every component theorem as an explicit parameter.
In particular the quantitative weighted moment <= 16 is NOT proved here.
This conditional assembly is not intended as a separate public submission.

The coefficients are a single common witness throughout.  The transfer
parameter has the exact positive-real-cutoff signature of the accepted result.
Only the final adapter converts its floors to natural division.
-/

/-- Final arithmetic assembly for one fixed coefficient witness. -/
theorem large_range_of_harmonic_inputs
    (h : ArithmeticFunction ℝ)
    (hmass : HasSum (fun n : ℕ => h n) 1)
    (hlog : Summable (fun n : ℕ => h n * Real.log (n : ℝ)))
    (hweight : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)))
    (hconvolution : ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then (1 : ℝ) / Nat.totient n else 0) =
        ∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ))
    (htransfer : ∀ (g : ℕ → ℝ) (g0 : g 0 = 0)
      (gmass : HasSum g 1)
      (glog : Summable (fun d : ℕ => g d * Real.log (d : ℝ)))
      (gweight : Summable (fun d : ℕ => |g d| * (d : ℝ) ^ (2 / 5 : ℝ)))
      (x : ℝ), 0 < x →
      |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
          g d * (harmonic ⌊x / (d : ℝ)⌋₊ : ℝ)) -
          (Real.log x + Real.eulerMascheroniConstant -
            ∑' d : ℕ, g d * Real.log (d : ℝ))| ≤
        (4 / 5 : ℝ) * x ^ (-(2 / 5 : ℝ)) *
          ∑' d : ℕ, |g d| * (d : ℝ) ^ (2 / 5 : ℝ))
    (hlog_identity : -(∑' n : ℕ, h n * Real.log (n : ℝ)) =
      ∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
    (hprime_constant : Real.eulerMascheroniConstant +
      (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        (67 / 50 : ℝ))
    (hweighted_bound : (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ≤ 16)
    (hnumeric : ∀ x : ℝ, 142300 ≤ x →
      (67 / 50 : ℝ) + (64 / 5 : ℝ) * x ^ (-(2 / 5 : ℝ)) ≤ (3677 / 2500 : ℝ))
    (N : ℕ) (hN : 142300 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4708 := by
  have hNR : (142300 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have herr := htransfer (fun n => h n) h.map_zero hmass hlog hweight (N : ℝ) hNpos
  simp only [Nat.floor_natCast, Nat.floor_div_eq_div] at herr
  rw [← hconvolution N] at herr
  have hcenter : Real.eulerMascheroniConstant -
      (∑' n : ℕ, h n * Real.log (n : ℝ)) ≤ (67 / 50 : ℝ) := by
    rw [sub_eq_add_neg, hlog_identity]
    exact hprime_constant
  have hcoefficient_nonneg :
      (0 : ℝ) ≤ (4 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ)) := by positivity
  have herror_bound :
      (4 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ)) *
          (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ≤
        (64 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ)) := by
    calc
      _ ≤ ((4 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ))) * 16 :=
        mul_le_mul_of_nonneg_left hweighted_bound hcoefficient_nonneg
      _ = _ := by ring
  have hupper := (le_abs_self
    ((∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then (1 : ℝ) / Nat.totient n else 0) -
      (Real.log (N : ℝ) + Real.eulerMascheroniConstant -
        ∑' d : ℕ, h d * Real.log (d : ℝ)))).trans (herr.trans herror_bound)
  have hslack := hnumeric (N : ℝ) hNR
  calc
    _ ≤ Real.log (N : ℝ) + (3677 / 2500 : ℝ) := by linarith
    _ = Real.log (N : ℝ) + 1.4708 := by norm_num

/-- Route-level adapter: the accepted existential construction, qualitative
moments, and error-transfer interfaces combine with explicit quantitative
inputs. No coefficient is replaced by a different existential witness. -/
theorem large_range_from_component_interfaces
    (hexists : ∃ h : ArithmeticFunction ℝ, h.IsMultiplicative ∧
      (∀ p : ℕ, Nat.Prime p →
        h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
        h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) ∧
      (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) ∧
      (∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N,
          if Squarefree n then (1 : ℝ) / Nat.totient n else 0) =
        ∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ)))
    (hmoments : ∀ (h : ArithmeticFunction ℝ), h.IsMultiplicative →
      (∀ p : ℕ, Nat.Prime p →
        h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
        h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) →
      (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) →
      HasSum (fun n : ℕ => h n) 1 ∧
        Summable (fun n : ℕ => h n * Real.log (n : ℝ)) ∧
        Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)))
    (htransfer : ∀ (g : ℕ → ℝ) (g0 : g 0 = 0)
      (gmass : HasSum g 1)
      (glog : Summable (fun d : ℕ => g d * Real.log (d : ℝ)))
      (gweight : Summable (fun d : ℕ => |g d| * (d : ℝ) ^ (2 / 5 : ℝ)))
      (x : ℝ), 0 < x →
      |(∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
          g d * (harmonic ⌊x / (d : ℝ)⌋₊ : ℝ)) -
          (Real.log x + Real.eulerMascheroniConstant -
            ∑' d : ℕ, g d * Real.log (d : ℝ))| ≤
        (4 / 5 : ℝ) * x ^ (-(2 / 5 : ℝ)) *
          ∑' d : ℕ, |g d| * (d : ℝ) ^ (2 / 5 : ℝ))
    (hlogmoment : ∀ (h : ArithmeticFunction ℝ), h.IsMultiplicative →
      (∀ p : ℕ, Nat.Prime p →
        h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
        h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) →
      (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) →
      Summable (fun n : ℕ => ‖h n‖) →
      Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖) →
      -(∑' n : ℕ, h n * Real.log (n : ℝ)) =
        ∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
    (hprime_constant : Real.eulerMascheroniConstant +
      (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        (67 / 50 : ℝ))
    (hweighted_bound : ∀ (h : ArithmeticFunction ℝ), h.IsMultiplicative →
      (∀ p : ℕ, Nat.Prime p →
        h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
        h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) →
      (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) →
      (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ≤ 16)
    (hnumeric : ∀ x : ℝ, 142300 ≤ x →
      (67 / 50 : ℝ) + (64 / 5 : ℝ) * x ^ (-(2 / 5 : ℝ)) ≤ (3677 / 2500 : ℝ))
    (N : ℕ) (hN : 142300 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4708 := by
  obtain ⟨h, hmul, hpv, hpz, hconvolution⟩ := hexists
  obtain ⟨hmass, hlog, hweight⟩ := hmoments h hmul hpv hpz
  have hnorm : Summable (fun n : ℕ => ‖h n‖) := by
    simpa only [Real.norm_eq_abs] using hmass.summable.abs
  have hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖) := by
    simpa only [Real.norm_eq_abs] using hlog.abs
  exact large_range_of_harmonic_inputs h hmass hlog hweight hconvolution htransfer
    (hlogmoment h hmul hpv hpz hnorm hlognorm) hprime_constant
    (hweighted_bound h hmul hpv hpz) hnumeric N hN

end RamareAnalytic

namespace RamareAnalytic

/-- Exact arithmetic slack for the proposed large-range analytic bounds. -/
theorem large_range_numeric_slack (N : ℝ) (hN : 142300 ≤ N) :
    (67 / 50 : ℝ) + (64 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) ≤ (3677 / 2500 : ℝ) := by
  have hNpos : 0 < N := by linarith
  have hp : 0 ≤ N ^ (2 / 5 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hpow : (N ^ (2 / 5 : ℝ)) ^ (5 : ℕ) = N ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hbase : (64000 / 654 : ℝ) ≤ N ^ (2 / 5 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 64000 / 654) hp
      (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hpow]
    have hsquare : (142300 : ℝ) ^ (2 : ℕ) ≤ N ^ (2 : ℕ) :=
      (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 142300) hNpos.le
        (by norm_num : (2 : ℕ) ≠ 0)).mpr hN
    norm_num at hsquare ⊢
    linarith
  have hinv : (N ^ (2 / 5 : ℝ))⁻¹ ≤ (654 / 64000 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hNpos _)).mpr
    nlinarith [hbase]
  rw [Real.rpow_neg hNpos.le]
  nlinarith [hinv]

end RamareAnalytic

private theorem ramare_prime_sum_eq_indicator :
    (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) =
      ∑' p : ℕ, if p.Prime then
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  classical
  let f : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  change (∑' p : {p : ℕ // p ∈ {q : ℕ | q.Prime}}, f p.val) =
    ∑' p : ℕ, if p.Prime then f p else 0
  calc
    _ = ∑' p : ℕ, Set.indicator {q : ℕ | q.Prime} f p :=
      tsum_subtype {p : ℕ | p.Prime} f
    _ = _ := by
      apply tsum_congr
      intro p
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]

theorem solution (N : ℕ) (hN : 142300 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) ≤
      Real.log (N : ℝ) + 1.4708 := by
  exact RamareAnalytic.large_range_from_component_interfaces
    RamareAnalytic.exists_squarefree_totient_harmonic_coefficients
    RamareAnalytic.moments_of_prime_power_values
    RamareAnalytic.harmonic_convolution_error_le
    (fun h hmul hpv hpz _ _ =>
      (RamareAnalytic.coefficient_logarithmic_moment h hmul hpv hpz).tsum_eq.symm)
    (by
      rw [ramare_prime_sum_eq_indicator]
      exact RamareAnalytic.global_logarithmic_constant_le.2)
    RamareAnalytic.weighted_moment_le_sixteen
    RamareAnalytic.large_range_numeric_slack N hN

#print axioms solution
