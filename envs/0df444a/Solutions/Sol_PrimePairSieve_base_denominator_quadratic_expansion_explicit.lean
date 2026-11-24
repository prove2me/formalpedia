-- Prove2me | solution 1 for PrimePairSieve.base_denominator_quadratic_expansion_explicit
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T11:27:12.518447+00:00
-- url     : https://prove2.me/submissions/1b3069ce-7cbd-4740-86cb-3e7cfddca6bc

import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_PrimePairSieve_double_harmonic_uniform_error_two
import Theorems.Thm_PrimePairSieve_exists_base_double_harmonic_coefficients
import Theorems.Thm_PrimePairSieve_base_correction_summability_and_mass
import Theorems.Thm_PrimePairSieve_base_correction_first_logarithmic_moment
import Theorems.Thm_PrimePairSieve_base_correction_second_logarithmic_moment
import Theorems.Thm_PrimePairSieve_base_correction_one_third_moment_bound
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false

open scoped BigOperators Topology
open Filter

namespace SiebertExplicit

theorem siebert_logPower_norm_summable
    (h : ArithmeticFunction ℝ) (α : ℝ) (hα : 0 < α)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ)^α)) (k : ℕ) :
    Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^k‖) := by
  by_cases hk : k = 0
  · subst k
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hw
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hp := Real.one_le_rpow hn1 hα.le
      simpa only [pow_zero, mul_one, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left hp (abs_nonneg (h n))
  · have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    let β : ℝ := α / k
    have hβ : 0 < β := div_pos hα hkR
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
      (hw.mul_left (1 / β^k))
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hlog := Real.log_natCast_le_rpow_div n hβ
      have hpow := pow_le_pow_left₀ hlog0 hlog k
      have hexp : β * (k : ℝ) = α := div_mul_cancel₀ α hkR.ne'
      have hpowEq : ((n : ℝ)^β / β)^k = (n : ℝ)^α / β^k := by
        rw [div_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n), hexp]
      rw [hpowEq] at hpow
      calc
        ‖h n * Real.log (n : ℝ)^k‖ = |h n| * Real.log (n : ℝ)^k := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hlog0 k)]
        _ ≤ |h n| * ((n : ℝ)^α / β^k) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg (h n))
        _ = (1 / β^k) * (|h n| * (n : ℝ)^α) := by ring

theorem siebert_finiteKernelConvolution_eq_tsum
    (h : ArithmeticFunction ℝ) (K : ℕ → ℝ) (hK0 : K 0 = 0) (N : ℝ) :
    (∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) =
      ∑' d : ℕ, h d * K ⌊N / (d : ℝ)⌋₊ := by
  symm
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hfloorlt : ⌊N⌋₊ < d := by
      simp only [Finset.mem_Icc, not_and] at hd
      exact lt_of_not_ge (hd hdpos)
    have hNd : N < (d : ℝ) := (Nat.floor_lt' hd0).mp hfloorlt
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
    have hz : ⌊N / (d : ℝ)⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr ((div_lt_one hdR).mpr hNd)
    simp [hz, hK0]

theorem siebert_quadraticKernelConvolution_error_le
    (K : ℕ → ℝ) (hK0 : K 0 = 0)
    (A B D E β : ℝ) (hβ : 0 < β)
    (hK : ∀ t : ℝ, 0 < t →
      |K ⌊t⌋₊ - (A * Real.log t ^ 2 + B * Real.log t + D)| ≤ E * t ^ (-β))
    (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ β))
    (N : ℝ) (hN : 0 < N) :
    |(∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) -
      ((A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
        (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
        A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2))| ≤
      E * N ^ (-β) * (∑' d : ℕ, |h d| * (d : ℝ)^β) := by
  have hnorm := siebert_logPower_norm_summable h β hβ hw 0
  simp only [pow_zero, mul_one] at hnorm
  have hmass := hnorm.of_norm.hasSum
  have hlognorm := siebert_logPower_norm_summable h β hβ hw 1
  simp only [pow_one] at hlognorm
  have hlog := hlognorm.of_norm.hasSum
  have hlog2 :=
    (siebert_logPower_norm_summable h β hβ hw 2).of_norm.hasSum
  let R : ℕ → ℝ := fun d => h d *
    (K ⌊N / (d : ℝ)⌋₊ -
      (A * Real.log (N / (d : ℝ))^2 + B * Real.log (N / (d : ℝ)) + D))
  let C : ℝ := E * N ^ (-β)
  have hpoint : ∀ d : ℕ, ‖R d‖ ≤ C * (|h d| * (d : ℝ)^β) := by
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [R]
    · have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
      have hb := hK (N / (d : ℝ)) (div_pos hN hdR)
      have hpow : (N / (d : ℝ)) ^ (-β) = N ^ (-β) * (d : ℝ)^β := by
        rw [Real.div_rpow hN.le hdR.le, Real.rpow_neg hdR.le, div_inv_eq_mul]
      calc
        ‖R d‖ = |h d| * |K ⌊N / (d : ℝ)⌋₊ -
          (A * Real.log (N / (d : ℝ))^2 + B * Real.log (N / (d : ℝ)) + D)| := by
            dsimp only [R]
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |h d| * (E * (N / (d : ℝ)) ^ (-β)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = C * (|h d| * (d : ℝ)^β) := by rw [hpow]; dsimp [C]; ring
  have hR : Summable R := (hw.mul_left C).of_norm_bounded hpoint
  have hbound : |∑' d : ℕ, R d| ≤ C * ∑' d : ℕ, |h d| * (d : ℝ)^β := by
    simpa only [Real.norm_eq_abs] using
      hR.hasSum.norm_le_of_bounded (hw.hasSum.mul_left C) hpoint
  have hdecomp :
      HasSum (fun d : ℕ => h d * K ⌊N / (d : ℝ)⌋₊)
        ((∑' d : ℕ, R d) +
          (A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
          (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
          A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2)) := by
    have hs := ((hR.hasSum.add
      (hmass.mul_left (A * Real.log N ^ 2 + B * Real.log N + D))).sub
      (hlog.mul_left (2 * A * Real.log N + B))).add (hlog2.mul_left A)
    apply hs.congr_fun
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [R]
    · dsimp [R]
      rw [Real.log_div hN.ne' (Nat.cast_ne_zero.mpr hd0)]
      ring
  have hcenter :
      (∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) -
        ((A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
          (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
          A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2)) = ∑' d : ℕ, R d := by
    rw [siebert_finiteKernelConvolution_eq_tsum h K hK0, hdecomp.tsum_eq]
    ring
  rw [hcenter]
  exact hbound

end SiebertExplicit

theorem siebert_base_expansion_explicit :
    ∃ B E : ℝ, 0 ≤ E ∧ E ≤ 600 ∧
      (2 * Real.eulerMascheroniConstant^2 +
        4 * Real.eulerMascheroniConstant *
          (2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
        ((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) ≤ B) ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) -
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨h, hmul, hpv, hpz, hfinite⟩ :=
    PrimePairSieve.exists_base_double_harmonic_coefficients
  obtain ⟨c, hc, _hcTendsto, hckernel⟩ :=
    PrimePairSieve.double_harmonic_uniform_error_two
  obtain ⟨hMsummable, hMle, _hMlt⟩ :=
    PrimePairSieve.base_correction_one_third_moment_bound h hmul hpv hpz
  obtain ⟨_hMassSummable, hmass⟩ :=
    PrimePairSieve.base_correction_summability_and_mass h hmul hpv hpz
  have hlogHas :=
    PrimePairSieve.base_correction_first_logarithmic_moment h hmul hpv hpz
  obtain ⟨_hLog2Summable, hlog2Has⟩ :=
    PrimePairSieve.base_correction_second_logarithmic_moment h hmul hpv hpz
  set M : ℝ := ∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ) with hM
  set B0 : ℝ :=
    2 * Real.eulerMascheroniConstant^2 +
      4 * Real.eulerMascheroniConstant *
        (2 * (∑' p : Nat.Primes,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
      ((2 * (∑' p : Nat.Primes,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
        (1 / 4 : ℝ) * Real.log 2^2 -
        (∑' p : Nat.Primes,
          (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
            ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) with hB0
  refine ⟨B0 - 4 * c, 2 * M, ?_, ?_, ?_, ?_⟩
  · rw [hM]
    exact mul_nonneg (by norm_num)
      (tsum_nonneg fun n => mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hMle' : M ≤ 7491 / 25 := by simpa only [hM] using hMle
    nlinarith
  · linarith [hc.2]
  · intro z hz
    have hkernel : ∀ t : ℝ, 0 < t →
        |(fun N : ℕ => ∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ)) ⌊t⌋₊ -
          ((1 / 2 : ℝ) * Real.log t^2 + 2 * Real.eulerMascheroniConstant * Real.log t +
            (Real.eulerMascheroniConstant^2 - 2 * c))| ≤
          2 * t ^ (-(1 / 3 : ℝ)) := by
      intro t ht
      have hcenter : Real.log t^2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log t +
          Real.eulerMascheroniConstant^2 - 2 * c =
          (1 / 2 : ℝ) * Real.log t^2 + 2 * Real.eulerMascheroniConstant * Real.log t +
            (Real.eulerMascheroniConstant^2 - 2 * c) := by ring
      rw [← hcenter]
      exact hckernel t ht
    have hconv : (∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) =
        ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, h d *
          (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ))
            ⌊z / (d : ℝ)⌋₊ := by
      simpa only [Nat.floor_div_natCast] using hfinite ⌊z⌋₊
    have he := SiebertExplicit.siebert_quadraticKernelConvolution_error_le
      (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ))
      (by simp)
      (1 / 2) (2 * Real.eulerMascheroniConstant)
      (Real.eulerMascheroniConstant^2 - 2 * c) 2 (1 / 3) (by norm_num)
      hkernel h hMsummable z hz
    have hm : (∑' n : ℕ, h n) = 1 / TaoFivePrimes.twinPrimeConstant :=
      hmass.tsum_eq
    have hl : (∑' n : ℕ, h n * Real.log (n : ℝ)) =
        -((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) /
          TaoFivePrimes.twinPrimeConstant) := hlogHas.tsum_eq
    have h2 : (∑' n : ℕ, h n * Real.log (n : ℝ)^2) =
        (((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) /
          TaoFivePrimes.twinPrimeConstant) := hlog2Has.tsum_eq
    rw [hm, hl, h2] at he
    have hcenter :
        ((1 / 2 : ℝ) * Real.log z^2 + 2 * Real.eulerMascheroniConstant * Real.log z +
            (Real.eulerMascheroniConstant^2 - 2 * c)) *
              (1 / TaoFivePrimes.twinPrimeConstant) -
          (2 * (1 / 2 : ℝ) * Real.log z + 2 * Real.eulerMascheroniConstant) *
            (-((2 * (∑' p : Nat.Primes,
                Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) /
              TaoFivePrimes.twinPrimeConstant)) +
          (1 / 2 : ℝ) *
            (((2 * (∑' p : Nat.Primes,
                Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
              (1 / 4 : ℝ) * Real.log 2^2 -
              (∑' p : Nat.Primes,
                (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
                  ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) /
              TaoFivePrimes.twinPrimeConstant) =
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + (B0 - 4 * c)) /
          (2 * TaoFivePrimes.twinPrimeConstant) := by
      rw [hB0]
      ring
    rw [hcenter] at he
    rw [← hconv] at he
    simpa only [hM, mul_assoc, mul_left_comm, mul_comm] using he

theorem solution :
    ∃ B E : ℝ, 0 ≤ E ∧ E ≤ 600 ∧
      (2 * Real.eulerMascheroniConstant^2 +
        4 * Real.eulerMascheroniConstant *
          (2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
        ((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) ≤ B) ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) -
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ))) :=
  siebert_base_expansion_explicit

#print axioms solution
