-- Prove2me | solution 1 for PrimePairSieve.double_harmonic_uniform_error_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T01:07:54.760984+00:00
-- url     : https://prove2.me/submissions/ee84ea99-b23a-487c-a766-ec42abd4b6d3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases



set_option autoImplicit false
open scoped BigOperators

/-!
Exact finite hyperbola splitting and a finite-centred error estimate.
The identity is the opening step of Riesel--Vaughan (1983), Lemma 1,
printed p.48. This file does not claim their 1.641 x^(-1/3) remainder.
No correction coefficient, convergence, or Stieltjes constant is assumed.

The definition doubleHarmonic below is identical to BaseConvolution.lean.
A combined source must retain exactly one copy of that declaration.
-/

namespace PrimePairConvolution

noncomputable def doubleHarmonic (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ)

private theorem sum_Icc_ite_le (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 N, if a ≤ m then f a else 0) =
      ∑ a ∈ Finset.Icc 1 m, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private theorem sum_Icc_mul_cut (N a : ℕ) (ha : 0 < a) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then f a * f b else 0) =
      f a * ∑ b ∈ Finset.Icc 1 (N / a), f b := by
  rw [← Finset.sum_filter]
  have hs : (Finset.Icc 1 N).filter (fun b => a * b ≤ N) =
      Finset.Icc 1 (N / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb, _⟩, hab⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hab)⟩
    · rintro ⟨hb, hab⟩
      exact ⟨⟨hb, hab.trans (Nat.div_le_self N a)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hab⟩
  rw [hs, Finset.mul_sum]

/-- Finite Dirichlet hyperbola splitting for an arbitrary real weight.
No sign assumption is needed, and the zero cutoff is included. -/
theorem finite_hyperbola (f : ℕ → ℝ) (N m : ℕ) (hmN : m ≤ N)
    (hm : m * m ≤ N) (hnext : N < (m + 1) * (m + 1)) :
    (∑ a ∈ Finset.Icc 1 N, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b) =
      2 * (∑ a ∈ Finset.Icc 1 m, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b) -
        (∑ a ∈ Finset.Icc 1 m, f a) ^ 2 := by
  classical
  let K : ℕ → ℕ → ℝ := fun a b => if a * b ≤ N then f a * f b else 0
  have hsplit (a b : ℕ) :
      K a b = (if a ≤ m then K a b else 0) +
        (if b ≤ m then K a b else 0) -
        (if a ≤ m ∧ b ≤ m then f a * f b else 0) := by
    by_cases ha : a ≤ m <;> by_cases hb : b ≤ m
    · have hab : a * b ≤ N := (Nat.mul_le_mul ha hb).trans hm
      simp [K, ha, hb, hab]
    · simp [ha, hb]
    · simp [ha, hb]
    · have hab : ¬ a * b ≤ N := by
        have hma : m + 1 ≤ a := by omega
        have hmb : m + 1 ≤ b := by omega
        exact not_le.mpr (hnext.trans_le (Nat.mul_le_mul hma hmb))
      simp [K, ha, hb, hab]
  have hsum :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, K a b) =
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if a ≤ m then K a b else 0) +
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if b ≤ m then K a b else 0) -
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if a ≤ m ∧ b ≤ m then f a * f b else 0) := by
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => hsplit a b))
  have hleft :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a ≤ m then K a b else 0) =
      ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 N, K a b := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N,
          if a ≤ m then (∑ b ∈ Finset.Icc 1 N, K a b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ≤ m <;> simp [ha]
      _ = _ := sum_Icc_ite_le N m hmN _
  have hright :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if b ≤ m then K a b else 0) =
      ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 N, K a b := by
    rw [Finset.sum_comm]
    convert hleft using 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [K, Nat.mul_comm, mul_comm]
  have hcorner :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a ≤ m ∧ b ≤ m then f a * f b else 0) =
      (∑ a ∈ Finset.Icc 1 m, f a) ^ 2 := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N,
          if a ≤ m then (∑ b ∈ Finset.Icc 1 m, f a * f b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ≤ m
        · simp only [ha, true_and, if_true]
          exact sum_Icc_ite_le N m hmN _
        · simp [ha]
      _ = ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 m, f a * f b :=
        sum_Icc_ite_le N m hmN _
      _ = _ := by rw [← Finset.sum_mul_sum, pow_two]
  have hstrip (r : ℕ) :
      (∑ a ∈ Finset.Icc 1 r, ∑ b ∈ Finset.Icc 1 N, K a b) =
      ∑ a ∈ Finset.Icc 1 r, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b := by
    apply Finset.sum_congr rfl
    intro a ha
    exact sum_Icc_mul_cut N a (Finset.mem_Icc.mp ha).1 f
  rw [hleft, hright, hcorner, hstrip N, hstrip m] at hsum
  linarith

private theorem harmonic_sum_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The exact sqrt-cutoff identity for the literal BaseConvolution kernel. -/
theorem doubleHarmonic_hyperbola (N : ℕ) :
    doubleHarmonic N =
      2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N),
        (harmonic (N / a) : ℝ) / (a : ℝ)) - (harmonic (Nat.sqrt N) : ℝ)^2 := by
  have h := finite_hyperbola (fun a => (a : ℝ)⁻¹) N (Nat.sqrt N)
    (Nat.sqrt_le_self N) (Nat.sqrt_le N) (Nat.lt_succ_sqrt N)
  simp only [← harmonic_sum_real] at h
  simpa only [doubleHarmonic, div_eq_mul_inv, mul_comm] using h

-- Adapted from the checked private harmonic_error_le_inverse in
-- discovery_ramare_large/HarmonicError.lean; no use of its public 2/5-power bound.
private theorem harmonic_interval_error (n : ℕ) (hn : 0 < n)
    (t : ℝ) (hnt : (n : ℝ) ≤ t) (htn : t < (n : ℝ) + 1) :
    |(harmonic n : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
      1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < t := hnR.trans_le hnt
  have hglo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  change (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) <
    Real.eulerMascheroniConstant at hglo
  have hghi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', hn.ne', if_false] at hghi
  have hloglo := Real.log_le_log hnR hnt
  have hloghi := Real.log_le_log ht htn.le
  have hgap : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < (n : ℝ) + 1) hnR)
    rw [Real.log_div (by positivity) hnR.ne'] at h
    have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp [hnR.ne'] <;> ring
    rwa [heq] at h
  apply abs_le.mpr
  constructor <;> linarith

private theorem harmonic_quotient_error (N a : ℕ) (ha : 0 < a) (haN : a ≤ N) :
    |(harmonic (N / a) : ℝ) - Real.log ((N : ℝ) / a) -
      Real.eulerMascheroniConstant| ≤ 2 * (a : ℝ) / N := by
  have hN : 0 < N := ha.trans_le haN
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : 1 ≤ (N : ℝ) / a := (le_div_iff₀ haR).mpr (by
    simpa only [one_mul] using (show (a : ℝ) ≤ (N : ℝ) by exact_mod_cast haN))
  have hfloor : ⌊(N : ℝ) / a⌋₊ = N / a := Nat.floor_div_eq_div N a
  have hk : 0 < N / a := by rw [← hfloor]; exact Nat.floor_pos.mpr ht
  have hnt : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
    rw [← hfloor]
    exact Nat.floor_le (by positivity)
  have htn : (N : ℝ) / a < ((N / a : ℕ) : ℝ) + 1 := by
    rw [← hfloor]
    exact Nat.lt_floor_add_one _
  have hk1 : (1 : ℝ) ≤ ((N / a : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ N / a by omega)
  have hmajor : (N : ℝ) ≤ 2 * (a : ℝ) * ((N / a : ℕ) : ℝ) := by
    have hlt := (div_lt_iff₀ haR).mp htn
    calc
      _ ≤ (((N / a : ℕ) : ℝ) + 1) * a := hlt.le
      _ ≤ (2 * ((N / a : ℕ) : ℝ)) * a :=
        mul_le_mul_of_nonneg_right (by linarith) haR.le
      _ = _ := by ring
  have hi : 1 / ((N / a : ℕ) : ℝ) ≤ 2 * (a : ℝ) / N := by
    apply (div_le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < ((N / a : ℕ) : ℝ)) hNR).mpr
    simpa only [one_mul] using hmajor
  exact (harmonic_interval_error (N / a) hk ((N : ℝ) / a) hnt htn).trans hi

/-- A finite-centred O(N^(-1/2)) error, without a Stieltjes-constant premise.
The centre still contains the explicit finite logarithmic sum at sqrt N. -/
theorem doubleHarmonic_finite_center_error (N : ℕ) (hN : 1 ≤ N) :
    |doubleHarmonic N -
      (2 * (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
       2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) -
       (harmonic (Nat.sqrt N) : ℝ)^2)| ≤ 4 * (Nat.sqrt N : ℝ) / N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let E : ℕ → ℝ := fun a =>
    ((harmonic (N / a) : ℝ) - Real.log ((N : ℝ) / a) -
      Real.eulerMascheroniConstant) / a
  have hterm : ∀ a ∈ Finset.Icc 1 (Nat.sqrt N), |E a| ≤ 2 / (N : ℝ) := by
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2.trans (Nat.sqrt_le_self N)
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
    dsimp only [E]
    rw [abs_div, abs_of_pos haR]
    calc
      _ ≤ (2 * (a : ℝ) / N) / a :=
        div_le_div_of_nonneg_right (harmonic_quotient_error N a ha0 haN) haR.le
      _ = 2 / (N : ℝ) := by field_simp [haR.ne', hNR.ne']
  have hsum : |∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a| ≤
      (Nat.sqrt N : ℝ) * (2 / (N : ℝ)) := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), |E a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (2 / (N : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = _ := by simp
  have hdecomp :
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (harmonic (N / a) : ℝ) / a) =
      (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) +
      ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a := by
    conv_rhs =>
      rw [harmonic_sum_real, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
    dsimp only [E]
    rw [Real.log_div hNR.ne' haR.ne']
    ring
  rw [doubleHarmonic_hyperbola, hdecomp]
  have heq :
      2 * ((Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
        (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) +
        ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a) -
      (harmonic (Nat.sqrt N) : ℝ)^2 -
      (2 * (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
        2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) -
        (harmonic (Nat.sqrt N) : ℝ)^2) =
      2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ((Nat.sqrt N : ℝ) * (2 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end PrimePairConvolution



set_option autoImplicit false
open scoped BigOperators Topology
open Filter Set MeasureTheory

/-!
Construction of the first Stieltjes constant from finite log-weighted harmonic
sums, with an explicit elementary remainder. The convention is
gamma_1 = lim_n (sum_{a=1}^n log(a)/a - log(n)^2/2), as in Riesel--Vaughan
(1983), equation (2.1), printed p.45. No numerical value, asymptotic estimate,
Euler--Maclaurin formula, or sieve-coefficient hypothesis is assumed.

-/

namespace PrimePairConvolution

noncomputable def logWeightedHarmonic (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, Real.log (i + 1 : ℕ) / (i + 1 : ℕ)

theorem logWeightedHarmonic_eq_sum_Icc (n : ℕ) :
    logWeightedHarmonic n =
      ∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a := by
  rw [logWeightedHarmonic, Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun a : ℕ => Real.log (a : ℝ) / a) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

private theorem logWeightedHarmonic_succ (n : ℕ) :
    logWeightedHarmonic (n + 1) = logWeightedHarmonic n +
      Real.log (n + 1 : ℕ) / (n + 1 : ℕ) := by
  simp only [logWeightedHarmonic, Finset.sum_range_succ]

noncomputable def firstStieltjesSeq (n : ℕ) : ℝ :=
  logWeightedHarmonic n - Real.log (n : ℝ)^2 / 2

private theorem log_div_self_antitone_three :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici 3) := by
  apply Real.log_div_self_antitoneOn.mono
  intro x hx
  exact Real.exp_one_lt_three.le.trans hx

private theorem integral_log_div_self {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, Real.log x / x) =
      Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  have hx0 : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have : 3 ≤ x := ha.trans hx.1
    linarith
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log x ^ 2 / 2)
  · intro x hx
    apply (((Real.hasDerivAt_log (hx0 x hx)).fun_pow 2).div_const 2).congr_deriv
    norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  · apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact log_div_self_antitone_three.mono (fun x hx => ha.trans hx.1)

/-- One-step errors lie between zero and an explicit telescoping difference. -/
theorem firstStieltjesSeq_step (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ firstStieltjesSeq n - firstStieltjesSeq (n + 1) ∧
    firstStieltjesSeq n - firstStieltjesSeq (n + 1) ≤
      Real.log (n : ℝ) / n - Real.log (n + 1 : ℕ) / (n + 1 : ℕ) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hf : AntitoneOn (fun x : ℝ => Real.log x / x)
      (Set.Icc (n : ℝ) ((n : ℝ) + (1 : ℕ))) :=
    log_div_self_antitone_three.mono (fun x hx => hnR.trans hx.1)
  have hlo := hf.sum_le_integral (a := 1)
  have hup := hf.integral_le_sum (a := 1)
  have hi := integral_log_div_self hnR
    (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
  norm_num only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Nat.zero_add, add_zero] at hlo hup
  rw [hi] at hlo hup
  simp only [firstStieltjesSeq, logWeightedHarmonic_succ, Nat.cast_add,
    Nat.cast_one]
  constructor <;> linarith

private theorem firstStieltjesSeq_shift_antitone :
    Antitone (fun n : ℕ => firstStieltjesSeq (n + 3)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := (firstStieltjesSeq_step (n + 3) (by omega)).1
  have he : n + 1 + 3 = n + 3 + 1 := by omega
  rw [he]
  linarith

private theorem firstStieltjesSeq_lower_shift_monotone :
    Monotone (fun n : ℕ => firstStieltjesSeq (n + 3) -
      Real.log (n + 3 : ℕ) / (n + 3 : ℕ)) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := (firstStieltjesSeq_step (n + 3) (by omega)).2
  have he : n + 1 + 3 = n + 3 + 1 := by omega
  rw [he]
  linarith

private theorem firstStieltjesSeq_lower_le (n : ℕ) :
    firstStieltjesSeq (n + 3) - Real.log (n + 3 : ℕ) / (n + 3 : ℕ) ≤
      firstStieltjesSeq (n + 3) := by
  have hlog : 0 ≤ Real.log (n + 3 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 3 by omega))
  have hdiv : 0 ≤ Real.log (n + 3 : ℕ) / (n + 3 : ℕ) :=
    div_nonneg hlog (Nat.cast_nonneg _)
  linarith

private theorem firstStieltjesSeq_cross (n k : ℕ) :
    firstStieltjesSeq (n + 3) - Real.log (n + 3 : ℕ) / (n + 3 : ℕ) ≤
      firstStieltjesSeq (k + 3) := by
  exact (firstStieltjesSeq_lower_shift_monotone (le_max_left n k)).trans
    ((firstStieltjesSeq_lower_le (max n k)).trans
      (firstStieltjesSeq_shift_antitone (le_max_right n k)))

private theorem firstStieltjesSeq_bddBelow :
    BddBelow (Set.range (fun n : ℕ => firstStieltjesSeq (n + 3))) := by
  refine ⟨firstStieltjesSeq 3 - Real.log 3 / 3, ?_⟩
  rintro _ ⟨n, rfl⟩
  simpa only [Nat.zero_add, Nat.cast_ofNat] using firstStieltjesSeq_cross 0 n

/-- The first Stieltjes constant in the log-weighted-sum convention. -/
noncomputable def firstStieltjesConstant : ℝ :=
  ⨅ n : ℕ, firstStieltjesSeq (n + 3)

/-- Convergence is proved from the concrete elementary two-sequence enclosure. -/
theorem tendsto_firstStieltjesSeq :
    Tendsto firstStieltjesSeq atTop (𝓝 firstStieltjesConstant) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  exact tendsto_atTop_ciInf firstStieltjesSeq_shift_antitone firstStieltjesSeq_bddBelow

/-- Explicit one-sided remainder for all natural cutoffs at least three. -/
theorem firstStieltjesSeq_error (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ firstStieltjesSeq n - firstStieltjesConstant ∧
    firstStieltjesSeq n - firstStieltjesConstant ≤ Real.log (n : ℝ) / n := by
  have he : n - 3 + 3 = n := Nat.sub_add_cancel hn
  have hupper : firstStieltjesConstant ≤ firstStieltjesSeq n := by
    unfold firstStieltjesConstant
    simpa only [he] using ciInf_le firstStieltjesSeq_bddBelow (n - 3)
  have hlower : firstStieltjesSeq n - Real.log (n : ℝ) / n ≤
      firstStieltjesConstant := by
    unfold firstStieltjesConstant
    apply le_ciInf
    intro k
    simpa only [he] using firstStieltjesSeq_cross (n - 3) k
  constructor <;> linarith

/-- Literal finite-sum form used by the double-harmonic estimate. -/
theorem logWeightedHarmonic_error (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a) -
      Real.log (n : ℝ)^2 / 2 - firstStieltjesConstant ∧
    (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a) -
      Real.log (n : ℝ)^2 / 2 - firstStieltjesConstant ≤ Real.log (n : ℝ) / n := by
  simpa only [firstStieltjesSeq, logWeightedHarmonic_eq_sum_Icc] using
    firstStieltjesSeq_error n hn

end PrimePairConvolution


/-!
Append to checked LogWeightedHarmonic.lean (with the EulerMascheroni and
Analysis.SpecificLimits.Basic imports). These first endpoint corrections are
proved by finite logarithm bounds and telescoping, without assuming an
Euler--Maclaurin expansion or differentiating an infinite series.
-/

namespace PrimePairConvolution

private theorem telescoping_abs_le_limit
    (q b : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 c))
    (hb : ∀ j, n ≤ j → 0 ≤ b j)
    (hstep : ∀ j, n ≤ j → |q j - q (j+1)| ≤ b j - b (j+1)) :
    |q n - c| ≤ b n := by
  have hd (k : ℕ) : |q n - q (n+k)| ≤ b n - b (n+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ |q n - q (n+k)| + |q (n+k) - q (n+k+1)| :=
          abs_sub_le _ _ _
        _ ≤ (b n - b (n+k)) + (b (n+k) - b (n+k+1)) :=
          add_le_add ih (hstep (n+k) (by omega))
        _ = _ := by simp only [Nat.add_succ]; ring
  have hqshift : Filter.Tendsto (fun k : ℕ => q (n+k)) Filter.atTop (𝓝 c) := by
    simpa only [Function.comp_def, Nat.add_comm] using hq.comp (Filter.tendsto_add_atTop_nat n)
  apply le_of_tendsto' (tendsto_const_nhds.sub hqshift).abs
  intro k
  exact (hd k).trans (sub_le_self _ (hb (n+k) (by omega)))

/-- The endpoint-average gap for log(1+1/x), bounded by a rational expression. -/
private theorem logarithm_trapezoid_gap (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (1/x + 1/(x+1))/2 - Real.log ((x+1)/x) ∧
    (1/x + 1/(x+1))/2 - Real.log ((x+1)/x) ≤
      1/(2*x*(x+1)*(2*x+1)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hx2 : 0 < 2*x+1 := by linarith
  let z : ℝ := 1/(2*x+1)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z < 1 := (div_lt_one hx2).mpr (by linarith)
  have hzd : 1-z ≠ 0 := by linarith
  have hzs : 1-z^2 ≠ 0 := by nlinarith
  have heq : (1+z)/(1-z) = (x+1)/x := by
    apply (div_eq_iff hzd).mpr
    dsimp [z]
    field_simp [hx0.ne', hx2.ne']
    <;> ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 1
  have hup := Real.log_div_le_sum_range_add hz0 hz1 0
  norm_num only [Finset.sum_range_one, Finset.sum_range_zero, Nat.mul_zero,
    Nat.zero_add, zero_add, pow_one, Nat.cast_one, div_one] at hlo hup
  rw [heq] at hlo hup
  have hupper : 2*(z/(1-z^2)) = (1/x+1/(x+1))/2 := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hzs).mpr
    dsimp [z]
    field_simp [hx0.ne', hx1.ne', hx2.ne']
    <;> ring
  have hgap : (1/x+1/(x+1))/2 - 2*z = 1/(2*x*(x+1)*(2*x+1)) := by
    dsimp [z]
    field_simp [hx0.ne', hx1.ne', hx2.ne']
    <;> ring
  constructor <;> linarith

private theorem reciprocal_envelope_step (x : ℝ) (hx : 1 ≤ x) :
    1/(2*x*(x+1)*(2*x+1)) ≤ 1/(4*x^2)-1/(4*(x+1)^2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hx2 : 0 < 2*x+1 := by linarith
  have heq : (1/(4*x^2)-1/(4*(x+1)^2)) - 1/(2*x*(x+1)*(2*x+1)) =
      (2*x^2+2*x+1)/(4*x^2*(x+1)^2*(2*x+1)) := by
    field_simp [hx0.ne', hx1.ne', hx2.ne']
    <;> ring
  have hpos : 0 ≤ (2*x^2+2*x+1)/(4*x^2*(x+1)^2*(2*x+1)) := by positivity
  linarith

/-- The actual harmonic sum has its first endpoint correction with a quadratic error. -/
theorem harmonic_first_correction_error (n : ℕ) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant -
      1/(2*(n : ℝ))| ≤ 1/(4*(n : ℝ)^2) := by
  let q : ℕ → ℝ := fun j => (harmonic j : ℝ)-Real.log (j : ℝ)-1/(2*(j : ℝ))
  let b : ℕ → ℝ := fun j => 1/(4*(j : ℝ)^2)
  have hlim : Filter.Tendsto q Filter.atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hc : Filter.Tendsto (fun j : ℕ => 1/(2*(j : ℝ))) Filter.atTop (𝓝 (0:ℝ)) := by
      convert tendsto_const_div_atTop_nhds_zero_nat (1/2 : ℝ) using 1 <;> ext j <;> ring
    change Filter.Tendsto (fun j : ℕ =>
      (harmonic j : ℝ)-Real.log (j : ℝ)-1/(2*(j : ℝ)))
      Filter.atTop (𝓝 Real.eulerMascheroniConstant)
    simpa only [sub_zero] using Real.tendsto_harmonic_sub_log.sub hc
  have hstep : ∀ j, n ≤ j → |q j-q (j+1)| ≤ b j-b (j+1) := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hn.trans hj
    have hj0 : (j : ℝ) ≠ 0 := by linarith
    have hjp : (j : ℝ)+1 ≠ 0 := by linarith
    have hgap := logarithm_trapezoid_gap (j : ℝ) hj1
    have heq : q j-q (j+1) =
        -((1/(j : ℝ)+1/((j : ℝ)+1))/2-Real.log (((j : ℝ)+1)/j)) := by
      simp only [q, harmonic_succ, Rat.cast_add, Rat.cast_inv,
        Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
      rw [Real.log_div hjp hj0]
      field_simp [hj0, hjp]
      <;> ring
    rw [heq, abs_neg, abs_of_nonneg hgap.1]
    exact hgap.2.trans (by simpa only [b, Nat.cast_add, Nat.cast_one] using
      reciprocal_envelope_step (j : ℝ) hj1)
  have he := telescoping_abs_le_limit q b Real.eulerMascheroniConstant n hlim
    (fun j hj => by dsimp [b]; positivity) hstep
  convert he using 1 <;> dsimp [q, b] <;> congr 1 <;> ring

private theorem log_weighted_correction_step (x : ℝ) (hx : 1 ≤ x) :
    |Real.log ((x+1)/x) * (Real.log x + Real.log ((x+1)/x)/2) -
      (Real.log x/x + Real.log (x+1)/(x+1))/2| ≤
      (1+Real.log x)/(4*x^2) - (1+Real.log (x+1))/(4*(x+1)^2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hx2 : 0 < 2*x+1 := by linarith
  let L := Real.log x
  let d := Real.log ((x+1)/x)
  let T := (1/x+1/(x+1))/2-d
  have hL : 0 ≤ L := Real.log_nonneg hx
  have hd0 : 0 ≤ d := Real.log_nonneg ((le_div_iff₀ hx0).mpr (by linarith))
  have hlog : Real.log (x+1) = L+d := by dsimp [L, d]; rw [Real.log_div hx1.ne' hx0.ne']; ring
  have hT := logarithm_trapezoid_gap x hx
  change 0 ≤ T ∧ T ≤ 1/(2*x*(x+1)*(2*x+1)) at hT
  have hdu : d ≤ 1/x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
    have heq : (x+1)/x-1=1/x := by field_simp [hx0.ne']; ring
    simpa only [heq, d] using h
  have hdl : 1/(x+1) ≤ d := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
    have heq : 1-((x+1)/x)⁻¹=1/(x+1) := by field_simp [hx0.ne',hx1.ne']; ring
    simpa only [heq, d] using h
  have hdiff : d-1/(x+1) ≤ 1/(2*x*(x+1)) := by
    have heq : (1/x+1/(x+1))/2-1/(x+1)=1/(2*x*(x+1)) := by
      field_simp [hx0.ne',hx1.ne']; ring
    dsimp [T] at hT
    linarith
  have he : 0 ≤ d/2*(d-1/(x+1)) :=
    mul_nonneg (div_nonneg hd0 (by norm_num)) (sub_nonneg.mpr hdl)
  have heup : d/2*(d-1/(x+1)) ≤ 1/(4*x^2*(x+1)) := by
    have h := mul_le_mul hdu hdiff (sub_nonneg.mpr hdl) (by positivity : 0≤1/x)
    have heq : (1/x)*(1/(2*x*(x+1)))/2 = 1/(4*x^2*(x+1)) := by
      field_simp [hx0.ne',hx1.ne']; ring
    nlinarith
  have hid : d*(L+d/2)-(L/x+(L+d)/(x+1))/2 =
      -L*T+d/2*(d-1/(x+1)) := by dsimp [T]; ring
  have hab : |d*(L+d/2)-(L/x+(L+d)/(x+1))/2| ≤
      L/(2*x*(x+1)*(2*x+1))+1/(4*x^2*(x+1)) := by
    rw [hid]
    calc
      _ ≤ |-L*T|+|d/2*(d-1/(x+1))| := abs_add_le _ _
      _ = L*T+d/2*(d-1/(x+1)) := by
        rw [abs_mul, abs_neg, abs_of_nonneg hL, abs_of_nonneg hT.1, abs_of_nonneg he]
      _ ≤ L*(1/(2*x*(x+1)*(2*x+1)))+1/(4*x^2*(x+1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hT.2 hL) heup
      _ = _ := by ring
  have hrational : L/(2*x*(x+1)*(2*x+1))+1/(4*x^2*(x+1)) ≤
      (1+L)/(4*x^2)-(1+L+1/x)/(4*(x+1)^2) := by
    have heq : ((1+L)/(4*x^2)-(1+L+1/x)/(4*(x+1)^2)) -
        (L/(2*x*(x+1)*(2*x+1))+1/(4*x^2*(x+1))) =
        L*(2*x^2+2*x+1)/(4*x^2*(x+1)^2*(2*x+1)) := by
      field_simp [hx0.ne',hx1.ne',hx2.ne']; ring
    have hp : 0 ≤ L*(2*x^2+2*x+1)/(4*x^2*(x+1)^2*(2*x+1)) := by positivity
    linarith
  have hlast : (1+L)/(4*x^2)-(1+L+1/x)/(4*(x+1)^2) ≤
      (1+L)/(4*x^2)-(1+L+d)/(4*(x+1)^2) := by
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [hlog]
  simpa only [L, d, add_assoc] using hab.trans (hrational.trans hlast)

/-- The same constructed Stieltjes constant has a first endpoint correction.
Only finite logarithm bounds and the already proved limit are used. -/
theorem logWeightedHarmonic_first_correction_error (n : ℕ) (hn : 3 ≤ n) :
    |(∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ)/(a : ℝ)) -
      Real.log (n : ℝ)^2/2-firstStieltjesConstant-Real.log (n : ℝ)/(2*(n : ℝ))| ≤
      (1+Real.log (n : ℝ))/(4*(n : ℝ)^2) := by
  let q : ℕ → ℝ := fun j => firstStieltjesSeq j-Real.log (j : ℝ)/(2*(j : ℝ))
  let b : ℕ → ℝ := fun j => (1+Real.log (j : ℝ))/(4*(j : ℝ)^2)
  have hlim : Filter.Tendsto q Filter.atTop (𝓝 firstStieltjesConstant) := by
    have hc : Filter.Tendsto (fun j : ℕ => Real.log (j : ℝ)/(2*(j : ℝ)))
        Filter.atTop (𝓝 (0:ℝ)) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [Function.comp_def, pow_one, add_zero] using h
    change Filter.Tendsto (fun j : ℕ =>
      firstStieltjesSeq j-Real.log (j : ℝ)/(2*(j : ℝ)))
      Filter.atTop (𝓝 firstStieltjesConstant)
    simpa only [sub_zero] using tendsto_firstStieltjesSeq.sub hc
  have hstep : ∀ j, n ≤ j → |q j-q (j+1)| ≤ b j-b (j+1) := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hj0 : (j : ℝ) ≠ 0 := by linarith
    have hjp : (j : ℝ)+1 ≠ 0 := by linarith
    have h := log_weighted_correction_step (j : ℝ) hj1
    have hlog : Real.log (((j : ℝ)+1)/j) = Real.log ((j : ℝ)+1)-Real.log (j : ℝ) :=
      Real.log_div hjp hj0
    simp only [q, firstStieltjesSeq, logWeightedHarmonic_succ, b,
      Nat.cast_add, Nat.cast_one]
    convert h using 1 <;> rw [hlog] <;> congr 1 <;>
      field_simp [hj0, hjp] <;> ring
  have he := telescoping_abs_le_limit q b firstStieltjesConstant n hlim (by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hlog : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hj1
    dsimp [b]
    positivity) hstep
  convert he using 1 <;>
    simp only [q, b, firstStieltjesSeq, logWeightedHarmonic_eq_sum_Icc] <;>
    congr 1 <;> ring

end PrimePairConvolution


/-!
Append after the exact hyperbola and refined natural-cutoff lemmas.
Imports additionally needed: Mathlib.Analysis.SpecialFunctions.Pow.Real and
Mathlib.Algebra.BigOperators.Intervals. No source constant 1.641 is claimed.
The numerical coefficient below is obtained by elementary inequalities.
-/

namespace PrimePairConvolution

private theorem harmonic_floor_refined_three (y : ℝ) (hy : 3 ≤ y) :
    |(harmonic ⌊y⌋₊ : ℝ)-Real.log y-Real.eulerMascheroniConstant| ≤
      1/(2*y)+(10/9 : ℝ)/y^2 := by
  let n := ⌊y⌋₊
  let x : ℝ := n
  have hy0 : 0 < y := by linarith
  have hn3 : 3 ≤ n := (Nat.le_floor_iff hy0.le).mpr (by exact_mod_cast hy)
  have hx3 : 3 ≤ x := by dsimp [x]; exact_mod_cast hn3
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ y := Nat.floor_le hy0.le
  have hyx : y < x+1 := Nat.lt_floor_add_one y
  have hratio : y ≤ (4/3 : ℝ)*x := by linarith
  have hsq : y^2 ≤ ((4/3 : ℝ)*x)^2 := pow_le_pow_left₀ hy0.le hratio 2
  have hA : 1/(2*x*y) ≤ (2/3 : ℝ)/y^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hy0)).mpr
    have h := mul_le_mul_of_nonneg_right hratio hy0.le
    nlinarith
  have hB : 1/(4*x^2) ≤ (4/9 : ℝ)/y^2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hy0)).mpr
    nlinarith
  have hsum : 1/(2*x*y)+1/(4*x^2) ≤ (10/9 : ℝ)/y^2 := by
    calc
      _ ≤ (2/3 : ℝ)/y^2+(4/9 : ℝ)/y^2 := add_le_add hA hB
      _ = _ := by ring
  have hdlo := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hx0)
  have hdhi := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [inv_div] at hdlo
  have he := harmonic_first_correction_error n (by omega)
  change |(harmonic n : ℝ)-Real.log x-Real.eulerMascheroniConstant-1/(2*x)| ≤
    1/(4*x^2) at he
  have hupper : 1/(2*x)+1/(4*x^2)-(1-x/y) ≤ 1/(2*y)+1/(4*x^2) := by
    have hid : (1/(2*x)+1/(4*x^2)-(1-x/y))-(1/(2*y)+1/(4*x^2)) =
        (y-x)*(1-2*x)/(2*x*y) := by field_simp [hx0.ne',hy0.ne']; ring
    have hneg : (y-x)*(1-2*x)/(2*x*y) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by positivity)
    linarith
  have hlower : (y/x-1)-1/(2*x)+1/(4*x^2) ≤
      1/(2*y)+1/(2*x*y)+1/(4*x^2) := by
    have hid : ((y/x-1)-1/(2*x)+1/(4*x^2))-
        (1/(2*y)+1/(2*x*y)+1/(4*x^2)) =
        (y-x-1)*(2*y+1)/(2*x*y) := by field_simp [hx0.ne',hy0.ne']; ring
    have hneg : (y-x-1)*(2*y+1)/(2*x*y) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity)
    linarith
  rw [Real.log_div hy0.ne' hx0.ne'] at hdlo hdhi
  have hr := abs_le.mp he
  apply abs_le.mpr
  constructor
  · change -(1/(2*y)+(10/9 : ℝ)/y^2) ≤
      (harmonic n : ℝ)-Real.log y-Real.eulerMascheroniConstant
    linarith
  · change (harmonic n : ℝ)-Real.log y-Real.eulerMascheroniConstant ≤ _
    have hsmall : 1/(4*x^2) ≤ (10/9 : ℝ)/y^2 := by
      have hz : 0 ≤ 1/(2*x*y) := by positivity
      linarith
    linarith

private theorem sum_Icc_cast_triangle (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (a : ℝ)) = (m : ℝ)*((m : ℝ)+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m+1), ih]
    push_cast
    ring

private theorem real_hyperbola_finite_center_refined (t : ℝ) (ht : 9 ≤ t) :
    let m := Nat.sqrt ⌊t⌋₊
    |doubleHarmonic ⌊t⌋₊ -
      (2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
        2*(∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) - (harmonic m : ℝ)^2)| ≤
      (m : ℝ)/t+(10/9 : ℝ)*(m : ℝ)*((m : ℝ)+1)/t^2 := by
  let m := Nat.sqrt ⌊t⌋₊
  change |doubleHarmonic ⌊t⌋₊ -
    (2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      2*(∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) - (harmonic m : ℝ)^2)| ≤ _
  have ht0 : 0 < t := by linarith
  have hn9 : 9 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0.le).mpr (by exact_mod_cast ht)
  have hm3 : 3 ≤ m := Nat.le_sqrt.mpr hn9
  have hm2 : (m : ℝ)^2 ≤ t := by
    have h : (m : ℝ)^2 ≤ (⌊t⌋₊ : ℝ) := by dsimp [m]; exact_mod_cast Nat.sqrt_le' ⌊t⌋₊
    exact h.trans (Nat.floor_le ht0.le)
  let E : ℕ → ℝ := fun a =>
    ((harmonic (⌊t⌋₊/a) : ℝ)-Real.log (t/a)-Real.eulerMascheroniConstant)/a
  have hterm : ∀ a ∈ Finset.Icc 1 m,
      |E a| ≤ 1/(2*t)+(10/9 : ℝ)*(a : ℝ)/t^2 := by
    intro a ha
    have ha0 : 0 < (a : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ha).1
    have ham : (a : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp ha).2
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hmul : 3*(a : ℝ) ≤ (m : ℝ)^2 := by
      calc
        _ ≤ 3*(m : ℝ) := mul_le_mul_of_nonneg_left ham (by norm_num)
        _ ≤ (m : ℝ)*(m : ℝ) := mul_le_mul_of_nonneg_right hmR (by linarith)
        _ = _ := by ring
    have harg : (3 : ℝ) ≤ t/a := (le_div_iff₀ ha0).mpr (hmul.trans hm2)
    have h := harmonic_floor_refined_three (t/a) harg
    rw [Nat.floor_div_natCast] at h
    dsimp [E]
    rw [abs_div, abs_of_pos ha0]
    calc
      _ ≤ (1/(2*(t/a))+(10/9 : ℝ)/(t/a)^2)/a := div_le_div_of_nonneg_right h ha0.le
      _ = _ := by field_simp [ha0.ne',ht0.ne'] <;> ring
  have hsum : |∑ a ∈ Finset.Icc 1 m, E a| ≤
      (m : ℝ)/(2*t)+(10/9 : ℝ)*((m : ℝ)*((m : ℝ)+1)/2)/t^2 := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 m, |E a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 m, (1/(2*t)+(10/9 : ℝ)*(a : ℝ)/t^2) := Finset.sum_le_sum hterm
      _ = _ := by
        have hlin : (∑ a ∈ Finset.Icc 1 m, (10/9 : ℝ)*(a : ℝ)/t^2) =
            (10/9 : ℝ)*((m : ℝ)*((m : ℝ)+1)/2)/t^2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum, sum_Icc_cast_triangle]
        rw [Finset.sum_add_distrib, hlin]
        simp
        <;> ring
  have hdecomp : (∑ a ∈ Finset.Icc 1 m, (harmonic (⌊t⌋₊/a) : ℝ)/a) =
      (Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
        (∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) +
        ∑ a ∈ Finset.Icc 1 m, E a := by
    conv_rhs => rw [harmonic_sum_real, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp ha).1)
    dsimp [E]
    rw [Real.log_div ht0.ne' ha0]
    ring
  rw [doubleHarmonic_hyperbola]
  change |2*(∑ a ∈ Finset.Icc 1 m, (harmonic (⌊t⌋₊/a) : ℝ)/a) -
    (harmonic m : ℝ)^2 -
    (2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      2*(∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) - (harmonic m : ℝ)^2)| ≤ _
  rw [hdecomp]
  have hid : 2*((Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      (∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) + ∑ a ∈ Finset.Icc 1 m, E a) -
      (harmonic m : ℝ)^2 -
      (2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      2*(∑ a ∈ Finset.Icc 1 m, Real.log (a : ℝ)/a) - (harmonic m : ℝ)^2) =
      2*(∑ a ∈ Finset.Icc 1 m, E a) := by ring
  rw [hid, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*((m : ℝ)/(2*t)+(10/9 : ℝ)*((m : ℝ)*((m : ℝ)+1)/2)/t^2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

private theorem refined_center_cancellation (m : ℕ) (hm : 3 ≤ m)
    (t : ℝ) (hlo : (m : ℝ)^2 ≤ t) (hhi : t < ((m : ℝ)+1)^2) :
    |(2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
        2*(∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ)/i) - (harmonic m : ℝ)^2) -
      (Real.log t^2/2+2*Real.eulerMascheroniConstant*Real.log t+
        Real.eulerMascheroniConstant^2-2*firstStieltjesConstant)| ≤
      (Real.log (m : ℝ)+7/4)/(m : ℝ)^2 := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have ht0 : 0 < t := (sq_pos_of_pos hm0).trans_le hlo
  let L := Real.log t
  let l := Real.log (m : ℝ)
  let a : ℝ := 1/m
  let u := L/2-l
  let e := (harmonic m : ℝ)-l-Real.eulerMascheroniConstant
  let r := e-a/2
  let s := (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ)/i)-l^2/2-firstStieltjesConstant
  let q := s-l*a/2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha3 : a ≤ (1/3 : ℝ) := one_div_le_one_div_of_le (by norm_num) hmR
  have hl0 : 0 ≤ l := Real.log_nonneg (by linarith)
  have hloglo : 2*l ≤ L := by
    have h := Real.log_le_log (sq_pos_of_pos hm0) hlo
    simpa only [Real.log_pow, Nat.cast_ofNat, l, L] using h
  have hloghi : L ≤ 2*Real.log ((m : ℝ)+1) := by
    have h := Real.log_le_log ht0 hhi.le
    simpa only [Real.log_pow, Nat.cast_ofNat, L] using h
  have hgap : Real.log ((m : ℝ)+1)-l ≤ a := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (m : ℝ)+1) hm0)
    rw [Real.log_div (by positivity) hm0.ne'] at h
    have hid : ((m : ℝ)+1)/m-1=a := by dsimp [a]; field_simp [hm0.ne']; ring
    simpa only [l, hid] using h
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hua : u ≤ a := by dsimp [u]; linarith
  have hr : |r| ≤ a^2/4 := by
    have hrid : r = (harmonic m : ℝ)-Real.log (m : ℝ)-
        Real.eulerMascheroniConstant-1/(2*(m : ℝ)) := by
      dsimp [r,e,a,l]
      field_simp [hm0.ne'] <;> ring
    have hbid : a^2/4 = 1/(4*(m : ℝ)^2) := by
      dsimp [a]
      field_simp [hm0.ne'] <;> ring
    rw [hrid,hbid]
    exact harmonic_first_correction_error m (by omega)
  have hq : |q| ≤ (1+l)*a^2/4 := by
    have hqid : q = (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ)/i)-
        Real.log (m : ℝ)^2/2-firstStieltjesConstant-Real.log (m : ℝ)/(2*(m : ℝ)) := by
      dsimp [q,s,a,l]
      field_simp [hm0.ne'] <;> ring
    have hbid : (1+l)*a^2/4 = (1+Real.log (m : ℝ))/(4*(m : ℝ)^2) := by
      dsimp [a,l]
      field_simp [hm0.ne'] <;> ring
    rw [hqid,hbid]
    exact logWeightedHarmonic_first_correction_error m hm
  have heabs : |e| ≤ (7/12 : ℝ)*a := by
    have heq : e=a/2+r := by dsimp [r]; ring
    rw [heq]
    have htri := abs_add_le (a/2) r
    rw [abs_of_nonneg (by positivity : 0≤a/2)] at htri
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha3)]
  have he2 : e^2 ≤ (49/144 : ℝ)*a^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg e) heabs 2
    norm_num only [sq_abs, mul_pow, show (7/12 : ℝ)^2=49/144 by norm_num] at h
    exact h
  have hbase0 : 0 ≤ 2*u*(a-u) :=
    mul_nonneg (mul_nonneg (by norm_num) hu0) (sub_nonneg.mpr hua)
  have hbase : 2*u*(a-u) ≤ a^2/2 := by nlinarith [sq_nonneg (2*u-a)]
  have hcross : |2*(l+2*u)*r| ≤ (l/2+a)*a^2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0≤2*(l+2*u))]
    have h := mul_le_mul_of_nonneg_left hr (by positivity : 0≤2*(l+2*u))
    have h2 := mul_le_mul_of_nonneg_right hua (sq_nonneg a)
    nlinarith
  have hid : (2*(L+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      2*(∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ)/i) - (harmonic m : ℝ)^2) -
      (L^2/2+2*Real.eulerMascheroniConstant*L+Real.eulerMascheroniConstant^2-
        2*firstStieltjesConstant) = 2*u*(a-u)+2*(l+2*u)*r-e^2-2*q := by
    dsimp [u,r,q,e,s]
    ring
  change |(2*(L+Real.eulerMascheroniConstant)*(harmonic m : ℝ) -
      2*(∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ)/i) - (harmonic m : ℝ)^2) -
      (L^2/2+2*Real.eulerMascheroniConstant*L+Real.eulerMascheroniConstant^2-
        2*firstStieltjesConstant)| ≤ _
  rw [hid]
  have htri : |2*u*(a-u)+2*(l+2*u)*r-e^2-2*q| ≤
      |2*u*(a-u)|+|2*(l+2*u)*r|+|e^2|+|2*q| := by
    have h1 := abs_sub (2*u*(a-u)+2*(l+2*u)*r-e^2) (2*q)
    have h2 := abs_sub (2*u*(a-u)+2*(l+2*u)*r) (e^2)
    have h3 := abs_add_le (2*u*(a-u)) (2*(l+2*u)*r)
    linarith
  have htwo : |2*q|=2*|q| := by rw [abs_mul]; norm_num
  rw [abs_of_nonneg hbase0, abs_sq, htwo] at htri
  have hqa := mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2)
  have ha2 := mul_le_mul_of_nonneg_right ha3 (sq_nonneg a)
  have hbound : |2*u*(a-u)+2*(l+2*u)*r-e^2-2*q| ≤ (l+7/4)*a^2 := by nlinarith
  calc
    _ ≤ (l+7/4)*a^2 := hbound
    _ = _ := by dsimp [a,l]; field_simp [hm0.ne'] <;> ring

private theorem log_three_le_nine_eighths : Real.log 3 ≤ (9/8 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤9/8) 5
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  exact (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3)).mpr (by linarith)

private theorem large_kernel_majorant_scaled (m t : ℝ) (hm : 3 ≤ m)
    (hlo : m^2 ≤ t) (hhi : t < (m+1)^2) :
    (m/t+(10/9 : ℝ)*m*(m+1)/t^2+(Real.log m+7/4)/m^2)*
      t^(1/3 : ℝ) ≤ (2245/1134 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := (sq_pos_of_pos hm0).trans_le hlo
  let v := m^(1/3 : ℝ)
  let w := t^(1/3 : ℝ)
  have hv0 : 0 < v := Real.rpow_pos_of_pos hm0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht0 _
  have hv3 : v^3=m := by dsimp [v]; rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  have hw3 : w^3=t := by dsimp [w]; rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hvlo : (7/5 : ℝ) ≤ v := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hv0.le (by decide : (3:ℕ)≠0)).mp
    rw [hv3]
    norm_num
    linarith
  have hv4 : (21/5 : ℝ) ≤ v^4 := by
    have h := mul_le_mul hm hvlo (by norm_num : (0:ℝ)≤7/5) hm0.le
    nlinarith [show v^4=m*v by rw [← hv3]; ring]
  have hvmw : v^2 ≤ w := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg v) hw0.le (by decide : (3:ℕ)≠0)).mp
    have he : (v^2)^3=m^2 := by rw [← hv3]; ring
    simpa only [he,hw3] using hlo
  have hwvm : w ≤ (4/3 : ℝ)*v^2 := by
    apply (pow_le_pow_iff_left₀ hw0.le (by positivity) (by decide : (3:ℕ)≠0)).mp
    have he : ((4/3 : ℝ)*v^2)^3=(64/27 : ℝ)*m^2 := by rw [← hv3]; ring
    rw [hw3,he]
    have hmp : m+1 ≤ (4/3 : ℝ)*m := by linarith
    have hsq := pow_le_pow_left₀ (by positivity : 0≤m+1) hmp 2
    nlinarith [sq_nonneg m]
  have hfirst : m/t*w ≤ 1/v := by
    have hpow := pow_le_pow_left₀ (sq_nonneg v) hvmw 2
    have hpoly : m*v*w ≤ t := by rw [← hv3,← hw3]; nlinarith [mul_le_mul_of_nonneg_right hpow hw0.le]
    calc
      m/t*w = (m*w)/t := by ring
      _ ≤ 1/v := (div_le_div_iff₀ ht0 hv0).mpr (by nlinarith only [hpoly])
  have hsecond : (10/9 : ℝ)*m*(m+1)/t^2*w ≤ (40/27 : ℝ)/v^4 := by
    have hpow := pow_le_pow_left₀ (sq_nonneg v) hvmw 5
    have hmp : m+1 ≤ (4/3 : ℝ)*m := by linarith
    have hp := mul_le_mul_of_nonneg_left hmp hm0.le
    have hp2 := mul_le_mul_of_nonneg_right hp (by positivity : 0≤w*v^4)
    have hp3 := mul_le_mul_of_nonneg_right hpow hw0.le
    have hkey : m^2*w*v^4 ≤ t^2 := by
      calc
        _ = (v^2)^5*w := by rw [← hv3]; ring
        _ ≤ w^5*w := hp3
        _ = t^2 := by rw [← hw3]; ring
    calc
      _ = ((10/9 : ℝ)*m*(m+1)*w)/t^2 := by ring
      _ ≤ (40/27 : ℝ)/v^4 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (pow_pos hv0 4)).mpr
        nlinarith
  have hthird : (Real.log m+7/4)/m^2*w ≤
      (4/3 : ℝ)*(Real.log m+7/4)/v^4 := by
    have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
    have h := mul_le_mul_of_nonneg_left hwvm (by positivity : 0≤(Real.log m+7/4)/m^2)
    calc
      _ ≤ (Real.log m+7/4)/m^2*((4/3 : ℝ)*v^2) := h
      _ = _ := by rw [← hv3]; field_simp [hv0.ne'] <;> ring
  have hlogratio : Real.log m/v^4 ≤ (15/56 : ℝ) := by
    have he : Real.exp ((4/3 : ℝ)⁻¹) ≤ 3 :=
      (Real.exp_le_exp.mpr (by norm_num : (4/3 : ℝ)⁻¹≤1)).trans Real.exp_one_lt_three.le
    have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : (0:ℝ)<4/3)
      (show Real.exp ((4/3 : ℝ)⁻¹) ≤ 3 from he)
      (show Real.exp ((4/3 : ℝ)⁻¹) ≤ m from he.trans hm) hm
    have hv4eq : v^4=m^(4/3 : ℝ) := by
      dsimp [v]; rw [← Real.rpow_natCast,← Real.rpow_mul hm0.le]; norm_num
    have hroot : (7/5 : ℝ) ≤ (3:ℝ)^(1/3 : ℝ) := by
      apply (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0:ℝ)<3)).mp
      rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
      norm_num
    have hden : (21/5 : ℝ) ≤ (3:ℝ)^(4/3 : ℝ) := by
      have hid : (3:ℝ)^(4/3 : ℝ)=3*(3:ℝ)^(1/3 : ℝ) := by
        rw [show (4/3 : ℝ)=1+1/3 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
      rw [hid]
      linarith
    rw [hv4eq]
    exact hmono.trans ((div_le_div₀ (by norm_num : (0:ℝ)≤9/8)
      log_three_le_nine_eighths (by norm_num : (0:ℝ)<21/5) hden).trans_eq (by norm_num))
  have hinv : 1/v ≤ (5/7 : ℝ) := (div_le_iff₀ hv0).mpr (by linarith)
  have hinv4 : 1/v^4 ≤ (5/21 : ℝ) := (div_le_iff₀ (pow_pos hv0 4)).mpr (by linarith)
  have hscale := add_le_add (add_le_add hfirst hsecond) hthird
  change (m/t+(10/9 : ℝ)*m*(m+1)/t^2+(Real.log m+7/4)/m^2)*w ≤ _
  have heq : 1/v+(40/27 : ℝ)/v^4+(4/3 : ℝ)*(Real.log m+7/4)/v^4 =
      1/v+(103/27 : ℝ)*(1/v^4)+(4/3 : ℝ)*(Real.log m/v^4) := by ring
  have hbound : 1/v+(40/27 : ℝ)/v^4+(4/3 : ℝ)*(Real.log m+7/4)/v^4 ≤
      (2245/1134 : ℝ) := by rw [heq]; linarith
  nlinarith

/-- A refined large-real-cutoff estimate for the actual constructed constant.
This coefficient is below2; it is not the source's sharper1.641. -/
theorem doubleHarmonic_large_real_cutoff_error (t : ℝ) (ht : 9 ≤ t) :
    |doubleHarmonic ⌊t⌋₊ -
      (Real.log t^2/2+2*Real.eulerMascheroniConstant*Real.log t+
        Real.eulerMascheroniConstant^2-2*firstStieltjesConstant)| ≤
      (2245/1134 : ℝ)*t^(-(1/3 : ℝ)) := by
  let m := Nat.sqrt ⌊t⌋₊
  have ht0 : 0 < t := by linarith
  have hn9 : 9 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0.le).mpr (by exact_mod_cast ht)
  have hm3 : 3 ≤ m := Nat.le_sqrt.mpr hn9
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm3
  have hlo : (m : ℝ)^2 ≤ t := by
    have h : (m : ℝ)^2 ≤ (⌊t⌋₊ : ℝ) := by dsimp [m]; exact_mod_cast Nat.sqrt_le' ⌊t⌋₊
    exact h.trans (Nat.floor_le ht0.le)
  have hhi : t < ((m : ℝ)+1)^2 := by
    have hnat := Nat.succ_le_iff.mpr (Nat.lt_succ_sqrt' ⌊t⌋₊)
    have hcast : (⌊t⌋₊ : ℝ)+1 ≤ ((m : ℝ)+1)^2 := by
      dsimp [m]
      exact_mod_cast hnat
    exact (Nat.lt_floor_add_one t).trans_le hcast
  have hf := real_hyperbola_finite_center_refined t ht
  have hc := refined_center_cancellation m hm3 t hlo hhi
  have htri := (abs_sub_le (doubleHarmonic ⌊t⌋₊)
    (2*(Real.log t+Real.eulerMascheroniConstant)*(harmonic m : ℝ)-
      2*(∑ i ∈ Finset.Icc 1 m,Real.log (i : ℝ)/i)-(harmonic m : ℝ)^2)
    (Real.log t^2/2+2*Real.eulerMascheroniConstant*Real.log t+
      Real.eulerMascheroniConstant^2-2*firstStieltjesConstant)).trans (add_le_add hf hc)
  have hw0 : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hscaled := (mul_le_mul_of_nonneg_right htri hw0.le).trans
    (large_kernel_majorant_scaled (m : ℝ) t hmR hlo hhi)
  have hdiv := (le_div_iff₀ hw0).mpr hscaled
  simpa only [Real.rpow_neg ht0.le,div_eq_mul_inv] using hdiv

end PrimePairConvolution




set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace PrimePairConvolution

private theorem quartic_certificate_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u^4 + 12*u^3 - 378*u^2 + 1620*u + 1188 := by
  by_cases h : u ≤ 1
  · have hs : u^2 ≤ u := by nlinarith
    have h3 : 0 ≤ u^3 := pow_nonneg hu 3
    have h4 : 0 ≤ u^4 := pow_nonneg hu 4
    nlinarith
  · have h1 : 1 ≤ u := le_of_lt (lt_of_not_ge h)
    have ha : 0 ≤ u^2 + 28*u - 2 := by nlinarith [sq_nonneg u]
    have hm := mul_nonneg ha (sq_nonneg (u-8))
    have hid : u^4 + 12*u^3 - 378*u^2 + 1620*u + 1188 =
        (u^2 + 28*u - 2)*(u-8)^2 + (4*u-51)^2/2 + 31/2 := by ring
    rw [hid]
    positivity

/-- An exponential majorant of the quadratic center in the empty-sum regime.
The numerical hypotheses are explicit until connected to the actual constants. -/
theorem quadratic_center_exp_bound (u g c : ℝ) (hu : 0 ≤ u)
    (hg0 : (1/2 : ℝ) ≤ g) (hg1 : g ≤ 2/3)
    (hc0 : -(1/6 : ℝ) ≤ c) (hc1 : c ≤ 0) :
    |u^2/2 - 2*g*u + g^2 - 2*c| ≤ 2 * Real.exp (u/3) := by
  have hg : 0 ≤ g := by linarith
  have hg2 : g^2 ≤ (4/9 : ℝ) := by nlinarith
  have he1 : 1 ≤ Real.exp (u/3) := Real.one_le_exp (by positivity)
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ u/3 by positivity) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := quartic_certificate_nonneg u hu
  have hpoly : u^2/2-u+7/9 ≤ 2*Real.exp (u/3) := by nlinarith
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (u-2*g)]
  · have hm : u ≤ 2*g*u := by nlinarith
    nlinarith

/-- For cutoffs below one, the double-harmonic sum is empty and its quadratic
center has the required uniform error envelope. -/
theorem quadratic_center_small_cutoff (t g c : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hg0 : (1/2 : ℝ) ≤ g) (hg1 : g ≤ 2/3)
    (hc0 : -(1/6 : ℝ) ≤ c) (hc1 : c ≤ 0) :
    |Real.log t^2/2 + 2*g*Real.log t + g^2 - 2*c| ≤
      2 * t ^ (-(1/3 : ℝ)) := by
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have h := quadratic_center_exp_bound (-Real.log t) g c (by linarith)
    hg0 hg1 hc0 hc1
  have he : t ^ (-(1/3 : ℝ)) = Real.exp ((-Real.log t)/3) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  rw [he]
  convert h using 1 <;> ring

end PrimePairConvolution




set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
open scoped BigOperators




namespace PrimePairConvolution

private def finiteKernelLogSeries (x : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range 24,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private def finiteKernelLogUpper (x : ℚ) : ℚ :=
  finiteKernelLogSeries x +
    2 * ((x - 1) / (x + 1)) ^ 49 / (1 - ((x - 1) / (x + 1)) ^ 2)

private theorem finiteKernelLogSeries_le (x : ℚ) (hx : 1 ≤ x) :
    (finiteKernelLogSeries x : ℝ) ≤ Real.log (x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hnonneg hlt 24
  rw [hratio] at h
  unfold finiteKernelLogSeries
  push_cast
  linarith

private theorem finiteKernelLog_le_upper (x : ℚ) (hx : 1 ≤ x) :
    Real.log (x : ℝ) ≤ (finiteKernelLogUpper x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add hnonneg hlt 24
  rw [hratio] at h
  calc
    Real.log (x : ℝ) = 2 * ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by ring
    _ ≤ 2 * ((∑ i ∈ Finset.range 24,
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ 49 /
          (1 - (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (finiteKernelLogUpper x : ℝ) := by
      unfold finiteKernelLogUpper finiteKernelLogSeries
      push_cast
      ring

private theorem finiteKernelLog_interval (x lo hi : ℚ) (hx : 1 ≤ x)
    (hlo : lo ≤ finiteKernelLogSeries x)
    (hhi : finiteKernelLogUpper x ≤ hi) :
    (lo : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (hi : ℝ) := by
  exact ⟨((Rat.cast_le (K := ℝ)).2 hlo).trans (finiteKernelLogSeries_le x hx),
    (finiteKernelLog_le_upper x hx).trans ((Rat.cast_le (K := ℝ)).2 hhi)⟩

private def finiteKernelRational (N : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 N, harmonic (N / a) / (a : ℚ)

private theorem finiteKernelRational_cast (N : ℕ) :
    (finiteKernelRational N : ℝ) = doubleHarmonic N := by
  simp only [finiteKernelRational, doubleHarmonic, Rat.cast_sum, Rat.cast_div,
    Rat.cast_natCast]


private theorem finiteKernelLog_certificate_1 :
    (0 : ℚ) ≤ finiteKernelLogSeries 1 ∧
      finiteKernelLogUpper 1 ≤ (0 : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_1 :
    (0 : ℝ) ≤ Real.log (1 : ℝ) ∧ Real.log (1 : ℝ) ≤ (0 : ℝ) := by
  have h := finiteKernelLog_interval 1 0 0 (by norm_num)
    finiteKernelLog_certificate_1.1 finiteKernelLog_certificate_1.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_2 :
    ((69/100) : ℚ) ≤ finiteKernelLogSeries 2 ∧
      finiteKernelLogUpper 2 ≤ ((7/10) : ℚ) := by decide +kernel

theorem finiteKernel_log_bounds_2 :
    ((69/100) : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ ((7/10) : ℝ) := by
  have h := finiteKernelLog_interval 2 (69/100) (7/10) (by norm_num)
    finiteKernelLog_certificate_2.1 finiteKernelLog_certificate_2.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_3 :
    ((109/100) : ℚ) ≤ finiteKernelLogSeries 3 ∧
      finiteKernelLogUpper 3 ≤ ((11/10) : ℚ) := by decide +kernel

theorem finiteKernel_log_bounds_3 :
    ((109/100) : ℝ) ≤ Real.log (3 : ℝ) ∧ Real.log (3 : ℝ) ≤ ((11/10) : ℝ) := by
  have h := finiteKernelLog_interval 3 (109/100) (11/10) (by norm_num)
    finiteKernelLog_certificate_3.1 finiteKernelLog_certificate_3.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_4 :
    ((69/50) : ℚ) ≤ finiteKernelLogSeries 4 ∧
      finiteKernelLogUpper 4 ≤ ((139/100) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_4 :
    ((69/50) : ℝ) ≤ Real.log (4 : ℝ) ∧ Real.log (4 : ℝ) ≤ ((139/100) : ℝ) := by
  have h := finiteKernelLog_interval 4 (69/50) (139/100) (by norm_num)
    finiteKernelLog_certificate_4.1 finiteKernelLog_certificate_4.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_5 :
    ((8/5) : ℚ) ≤ finiteKernelLogSeries 5 ∧
      finiteKernelLogUpper 5 ≤ ((161/100) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_5 :
    ((8/5) : ℝ) ≤ Real.log (5 : ℝ) ∧ Real.log (5 : ℝ) ≤ ((161/100) : ℝ) := by
  have h := finiteKernelLog_interval 5 (8/5) (161/100) (by norm_num)
    finiteKernelLog_certificate_5.1 finiteKernelLog_certificate_5.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_6 :
    ((179/100) : ℚ) ≤ finiteKernelLogSeries 6 ∧
      finiteKernelLogUpper 6 ≤ ((9/5) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_6 :
    ((179/100) : ℝ) ≤ Real.log (6 : ℝ) ∧ Real.log (6 : ℝ) ≤ ((9/5) : ℝ) := by
  have h := finiteKernelLog_interval 6 (179/100) (9/5) (by norm_num)
    finiteKernelLog_certificate_6.1 finiteKernelLog_certificate_6.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_7 :
    ((97/50) : ℚ) ≤ finiteKernelLogSeries 7 ∧
      finiteKernelLogUpper 7 ≤ ((39/20) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_7 :
    ((97/50) : ℝ) ≤ Real.log (7 : ℝ) ∧ Real.log (7 : ℝ) ≤ ((39/20) : ℝ) := by
  have h := finiteKernelLog_interval 7 (97/50) (39/20) (by norm_num)
    finiteKernelLog_certificate_7.1 finiteKernelLog_certificate_7.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_8 :
    ((207/100) : ℚ) ≤ finiteKernelLogSeries 8 ∧
      finiteKernelLogUpper 8 ≤ ((52/25) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_8 :
    ((207/100) : ℝ) ≤ Real.log (8 : ℝ) ∧ Real.log (8 : ℝ) ≤ ((52/25) : ℝ) := by
  have h := finiteKernelLog_interval 8 (207/100) (52/25) (by norm_num)
    finiteKernelLog_certificate_8.1 finiteKernelLog_certificate_8.2
  convert h using 1 <;> norm_num


private theorem finiteKernelLog_certificate_9 :
    ((219/100) : ℚ) ≤ finiteKernelLogSeries 9 ∧
      finiteKernelLogUpper 9 ≤ ((11/5) : ℚ) := by decide +kernel

private theorem finiteKernel_log_bounds_9 :
    ((219/100) : ℝ) ≤ Real.log (9 : ℝ) ∧ Real.log (9 : ℝ) ≤ ((11/5) : ℝ) := by
  have h := finiteKernelLog_interval 9 (219/100) (11/5) (by norm_num)
    finiteKernelLog_certificate_9.1 finiteKernelLog_certificate_9.2
  convert h using 1 <;> norm_num


private theorem finiteKernel_value_1 : doubleHarmonic 1 = (1 : ℝ) := by
  have h : finiteKernelRational 1 = (1 : ℚ) := by decide +kernel
  calc
    doubleHarmonic 1 = (finiteKernelRational 1 : ℝ) := (finiteKernelRational_cast 1).symm
    _ = ((1 : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = (1 : ℝ) := by norm_num


private theorem finiteKernel_value_2 : doubleHarmonic 2 = (2 : ℝ) := by
  have h : finiteKernelRational 2 = (2 : ℚ) := by decide +kernel
  calc
    doubleHarmonic 2 = (finiteKernelRational 2 : ℝ) := (finiteKernelRational_cast 2).symm
    _ = ((2 : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = (2 : ℝ) := by norm_num


private theorem finiteKernel_value_3 : doubleHarmonic 3 = ((8/3) : ℝ) := by
  have h : finiteKernelRational 3 = ((8/3) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 3 = (finiteKernelRational 3 : ℝ) := (finiteKernelRational_cast 3).symm
    _ = (((8/3) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((8/3) : ℝ) := by norm_num


private theorem finiteKernel_value_4 : doubleHarmonic 4 = ((41/12) : ℝ) := by
  have h : finiteKernelRational 4 = ((41/12) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 4 = (finiteKernelRational 4 : ℝ) := (finiteKernelRational_cast 4).symm
    _ = (((41/12) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((41/12) : ℝ) := by norm_num


private theorem finiteKernel_value_5 : doubleHarmonic 5 = ((229/60) : ℝ) := by
  have h : finiteKernelRational 5 = ((229/60) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 5 = (finiteKernelRational 5 : ℝ) := (finiteKernelRational_cast 5).symm
    _ = (((229/60) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((229/60) : ℝ) := by norm_num


private theorem finiteKernel_value_6 : doubleHarmonic 6 = ((269/60) : ℝ) := by
  have h : finiteKernelRational 6 = ((269/60) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 6 = (finiteKernelRational 6 : ℝ) := (finiteKernelRational_cast 6).symm
    _ = (((269/60) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((269/60) : ℝ) := by norm_num


private theorem finiteKernel_value_7 : doubleHarmonic 7 = ((2003/420) : ℝ) := by
  have h : finiteKernelRational 7 = ((2003/420) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 7 = (finiteKernelRational 7 : ℝ) := (finiteKernelRational_cast 7).symm
    _ = (((2003/420) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((2003/420) : ℝ) := by norm_num


private theorem finiteKernel_value_8 : doubleHarmonic 8 = ((2213/420) : ℝ) := by
  have h : finiteKernelRational 8 = ((2213/420) : ℚ) := by decide +kernel
  calc
    doubleHarmonic 8 = (finiteKernelRational 8 : ℝ) := (finiteKernelRational_cast 8).symm
    _ = (((2213/420) : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) h
    _ = ((2213/420) : ℝ) := by norm_num



private theorem finiteKernel_interval_scaled
    (g c t : ℝ) (n : ℕ) (K L U w : ℝ)
    (hglo : (1 : ℝ)/2 ≤ g) (hghi : g ≤ (2 : ℝ)/3)
    (hclo : -(1 : ℝ)/6 ≤ c) (hchi : c ≤ 0)
    (ht : 1 ≤ t) (hfloor : ⌊t⌋₊ = n) (hn : 1 ≤ n)
    (hK : doubleHarmonic n = K) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (n : ℝ)) (hU : Real.log ((n : ℝ)+1) ≤ U)
    (hw : 0 < w) (hcube : (n : ℝ)+1 ≤ w^3)
    (hpos0 : 0 ≤ K-(L^2/2+L+1/4))
    (hneg0 : 0 ≤ U^2/2+(4/3)*U+7/9-K)
    (hpos : (K-(L^2/2+L+1/4))*w ≤ 2)
    (hneg : (U^2/2+(4/3)*U+7/9-K)*w ≤ 2) :
    |doubleHarmonic ⌊t⌋₊ -
      ((Real.log t)^2/2+2*g*Real.log t+g^2-2*c)| * t^(1/3 : ℝ) ≤ 2 := by
  have ht0 : 0 < t := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnt : (n : ℝ) ≤ t := by simpa only [hfloor] using Nat.floor_le ht0.le
  have htn : t < (n : ℝ)+1 := by simpa only [hfloor] using Nat.lt_floor_add_one t
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogL : L ≤ Real.log t := hL.trans (Real.log_le_log hn0 hnt)
  have hlogU : Real.log t ≤ U := (Real.log_le_log ht0 htn.le).trans hU
  have hloSq : L^2 ≤ (Real.log t)^2 := pow_le_pow_left₀ hL0 hlogL 2
  have hhiSq : (Real.log t)^2 ≤ U^2 := pow_le_pow_left₀ hlog0 hlogU 2
  have hg0 : 0 ≤ g := by linarith
  have hgSqLo : (1 : ℝ)/4 ≤ g^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hglo 2
    norm_num at h
    exact h
  have hgSqHi : g^2 ≤ (4 : ℝ)/9 := by
    have h := pow_le_pow_left₀ hg0 hghi 2
    norm_num at h
    exact h
  have hgl := mul_le_mul_of_nonneg_right hglo hlog0
  have hgu := mul_le_mul_of_nonneg_right hghi hlog0
  let P := (Real.log t)^2/2+2*g*Real.log t+g^2-2*c
  have hPlo : L^2/2+L+1/4 ≤ P := by dsimp [P]; nlinarith
  have hPhi : P ≤ U^2/2+(4/3)*U+7/9 := by dsimp [P]; nlinarith
  let v := t^(1/3 : ℝ)
  have hv0 : 0 ≤ v := Real.rpow_nonneg ht0.le _
  have hv3 : v^3 = t := by
    dsimp [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hvw : v ≤ w := by
    apply (Real.rpow_le_rpow_iff hv0 hw.le (by norm_num : (0 : ℝ) < 3)).mp
    norm_num only [Real.rpow_ofNat]
    rw [hv3]
    exact htn.le.trans hcube
  have hplus : (K-P)*v ≤ 2 := by
    calc
      (K-P)*v ≤ (K-(L^2/2+L+1/4))*v :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hPlo K) hv0
      _ ≤ (K-(L^2/2+L+1/4))*w := mul_le_mul_of_nonneg_left hvw hpos0
      _ ≤ 2 := hpos
  have hminus : (P-K)*v ≤ 2 := by
    calc
      (P-K)*v ≤ (U^2/2+(4/3)*U+7/9-K)*v :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hPhi K) hv0
      _ ≤ (U^2/2+(4/3)*U+7/9-K)*w := mul_le_mul_of_nonneg_left hvw hneg0
      _ ≤ 2 := hneg
  have hab : |(K-P)*v| ≤ 2 := abs_le.mpr ⟨by nlinarith [hminus], hplus⟩
  rw [abs_mul, abs_of_nonneg hv0] at hab
  simpa only [hfloor, hK, P, v] using hab



/-- The eight nonempty small-cutoff intervals, with explicit constant ranges. -/
theorem doubleHarmonic_finite_cutoff_scaled (g c t : ℝ)
    (hglo : (1 : ℝ)/2 ≤ g) (hghi : g ≤ (2 : ℝ)/3)
    (hclo : -(1 : ℝ)/6 ≤ c) (hchi : c ≤ 0)
    (ht : 1 ≤ t) (ht9 : t < 9) :
    |doubleHarmonic ⌊t⌋₊ -
      ((Real.log t)^2/2+2*g*Real.log t+g^2-2*c)| * t^(1/3 : ℝ) ≤ 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hn1 : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).mpr (by simpa using ht)
  have hn9 : ⌊t⌋₊ < 9 := (Nat.floor_lt ht0).mpr (by simpa using ht9)
  interval_cases hfloor : ⌊t⌋₊

  · have hlog : Real.log ((1 : ℝ)+1) ≤ ((7/10) : ℝ) := by
      convert finiteKernel_log_bounds_2.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 1 1 0 (7/10) (13/10)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_1
      (by norm_num) (by simpa using finiteKernel_log_bounds_1.1) (by simpa using hlog) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((2 : ℝ)+1) ≤ ((11/10) : ℝ) := by
      convert finiteKernel_log_bounds_3.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 2 2 (69/100) (11/10) (3/2)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_2
      (by norm_num) finiteKernel_log_bounds_2.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((3 : ℝ)+1) ≤ ((139/100) : ℝ) := by
      convert finiteKernel_log_bounds_4.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 3 (8/3) (109/100) (139/100) (8/5)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_3
      (by norm_num) finiteKernel_log_bounds_3.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((4 : ℝ)+1) ≤ ((161/100) : ℝ) := by
      convert finiteKernel_log_bounds_5.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 4 (41/12) (69/50) (161/100) (7/4)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_4
      (by norm_num) finiteKernel_log_bounds_4.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((5 : ℝ)+1) ≤ ((9/5) : ℝ) := by
      convert finiteKernel_log_bounds_6.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 5 (229/60) (8/5) (9/5) (11/6)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_5
      (by norm_num) finiteKernel_log_bounds_5.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((6 : ℝ)+1) ≤ ((39/20) : ℝ) := by
      convert finiteKernel_log_bounds_7.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 6 (269/60) (179/100) (39/20) 2
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_6
      (by norm_num) finiteKernel_log_bounds_6.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((7 : ℝ)+1) ≤ ((52/25) : ℝ) := by
      convert finiteKernel_log_bounds_8.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 7 (2003/420) (97/50) (52/25) 2
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_7
      (by norm_num) finiteKernel_log_bounds_7.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h

  · have hlog : Real.log ((8 : ℝ)+1) ≤ ((11/5) : ℝ) := by
      convert finiteKernel_log_bounds_9.2 using 1 <;> norm_num
    have h := finiteKernel_interval_scaled g c t 8 (2213/420) (207/100) (11/5) (21/10)
      hglo hghi hclo hchi ht hfloor (by norm_num) finiteKernel_value_8
      (by norm_num) finiteKernel_log_bounds_8.1 hlog (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [hfloor] using h


/-- Sharp coefficient-two bound on the finite range 1 ≤ t < 9. -/
theorem doubleHarmonic_finite_cutoff_error (g c t : ℝ)
    (hglo : (1 : ℝ)/2 ≤ g) (hghi : g ≤ (2 : ℝ)/3)
    (hclo : -(1 : ℝ)/6 ≤ c) (hchi : c ≤ 0)
    (ht : 1 ≤ t) (ht9 : t < 9) :
    |doubleHarmonic ⌊t⌋₊ -
      ((Real.log t)^2/2+2*g*Real.log t+g^2-2*c)| ≤ 2*t^(-(1/3 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hv : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have h := (le_div_iff₀ hv).mpr
    (doubleHarmonic_finite_cutoff_scaled g c t hglo hghi hclo hchi ht ht9)
  simpa only [Real.rpow_neg ht0.le, div_eq_mul_inv] using h

end PrimePairConvolution



/-!
Append to the passed RefinedNaturalKernel source. Five-term rational logarithm
certificates locate the same constructed first Stieltjes constant. No numerical
value or constant enclosure is assumed.
-/

namespace PrimePairConvolution

private theorem stieltjes_log_two_bounds :
    (69/100 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (7/10 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) 5
  have hhi := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) 5
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

private theorem stieltjes_log_three_bounds :
    (109/100 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (11/10 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) 5
  have hhi := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) 5
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

/-- Coarse rational bounds on the actual common constant used by the kernel.
They follow from the first corrected log-harmonic remainder at n=3. -/
theorem firstStieltjesConstant_bounds :
    -(1/6 : ℝ) ≤ firstStieltjesConstant ∧ firstStieltjesConstant ≤ 0 := by
  have h2 := stieltjes_log_two_bounds
  have h3 := stieltjes_log_three_bounds
  have hslo : (109/100 : ℝ)^2 ≤ (Real.log 3)^2 :=
    pow_le_pow_left₀ (by norm_num) h3.1 2
  have hshi : (Real.log 3)^2 ≤ (11/10 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 3) h3.2 2
  have h := logWeightedHarmonic_first_correction_error 3 (by decide)
  rw [← logWeightedHarmonic_eq_sum_Icc] at h
  norm_num [logWeightedHarmonic, Finset.sum_range_succ] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> nlinarith

end PrimePairConvolution




namespace PrimePairConvolution

/-- A coefficient-two remainder at every positive real cutoff, with the actual
Euler--Mascheroni and constructed first Stieltjes constants. -/
theorem doubleHarmonic_sharp_real_cutoff_error (t : ℝ) (ht : 0 < t) :
    |doubleHarmonic ⌊t⌋₊ -
      (Real.log t^2/2+2*Real.eulerMascheroniConstant*Real.log t+
        Real.eulerMascheroniConstant^2-2*firstStieltjesConstant)| ≤
      2*t^(-(1/3 : ℝ)) := by
  have hglo : (1/2 : ℝ) ≤ Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant.le
  have hghi : Real.eulerMascheroniConstant ≤ (2/3 : ℝ) :=
    Real.eulerMascheroniConstant_lt_two_thirds.le
  have hc := firstStieltjesConstant_bounds
  by_cases ht1 : t < 1
  · have hfloor : ⌊t⌋₊ = 0 := by
      have h : ⌊t⌋₊ < 1 := (Nat.floor_lt ht.le).mpr (by simpa using ht1)
      omega
    have hK : doubleHarmonic ⌊t⌋₊ = 0 := by simp [hfloor, doubleHarmonic]
    rw [hK, zero_sub, abs_neg]
    exact quadratic_center_small_cutoff t Real.eulerMascheroniConstant
      firstStieltjesConstant ht ht1.le hglo hghi hc.1 hc.2
  · have htge : 1 ≤ t := le_of_not_gt ht1
    by_cases ht9 : t < 9
    · exact doubleHarmonic_finite_cutoff_error Real.eulerMascheroniConstant
        firstStieltjesConstant t hglo hghi (by simpa only [neg_div] using hc.1) hc.2 htge ht9
    · have hlarge := doubleHarmonic_large_real_cutoff_error t (le_of_not_gt ht9)
      exact hlarge.trans (mul_le_mul_of_nonneg_right
        (by norm_num : (2245/1134 : ℝ) ≤ 2) (Real.rpow_nonneg ht.le _))

end PrimePairConvolution

theorem solution :
    ∃ c : ℝ, (-(1 / 6 : ℝ) ≤ c ∧ c ≤ 0) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
            Real.log (n : ℝ)^2 / 2)
        Filter.atTop (𝓝 c) ∧
      ∀ t : ℝ, 0 < t →
        |(∑ a ∈ Finset.Icc 1 ⌊t⌋₊,
            (harmonic (⌊t⌋₊ / a) : ℝ) / (a : ℝ)) -
          (Real.log t^2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log t +
            Real.eulerMascheroniConstant^2 - 2 * c)| ≤
          2 * t ^ (-(1 / 3 : ℝ)) := by
  refine ⟨PrimePairConvolution.firstStieltjesConstant,
    PrimePairConvolution.firstStieltjesConstant_bounds, ?_, ?_⟩
  · have hc := PrimePairConvolution.tendsto_firstStieltjesSeq
    change Filter.Tendsto
      (fun n : ℕ => PrimePairConvolution.logWeightedHarmonic n -
        Real.log (n : ℝ)^2 / 2)
      Filter.atTop (𝓝 PrimePairConvolution.firstStieltjesConstant) at hc
    simpa only [PrimePairConvolution.logWeightedHarmonic_eq_sum_Icc] using hc
  · intro t ht
    simpa only [PrimePairConvolution.doubleHarmonic] using
      PrimePairConvolution.doubleHarmonic_sharp_real_cutoff_error t ht

#print axioms solution
