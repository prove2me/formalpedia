-- Prove2me | solution 1 for PrimePairSieve.double_harmonic_kernel_estimate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:46:34.626772+00:00
-- url     : https://prove2.me/submissions/44c3f13f-7b90-4383-bee2-7c395c222800

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.NormNum


set_option autoImplicit false
open scoped BigOperators

/-!
Exact finite hyperbola splitting and a finite-centred error estimate.
The identity is the opening step of Riesel--Vaughan (1983), Lemma 1,
printed p.48. This file does not claim their 1.641 x^(-1/3) remainder.
No correction coefficient, convergence, or Stieltjes constant is assumed.

The definition doubleHarmonic below is identical to BaseConvolution.lean.
A combined source must retain exactly one copy of that declaration.
Draft only: no compiler was invoked by the author of this file.
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

This is a standalone uncompiled draft; root owns all compiler runs.
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
Assemble the checked finite hyperbola estimate with the constructed first
Stieltjes constant. This fragment follows DoubleHarmonic.lean and
LogWeightedHarmonic.lean in one module. It assumes no asymptotic estimate.
The centre is Riesel--Vaughan (1983), Lemma 1, printed p.48; the elementary
explicit remainder here is different from their sharper numerical bound.
-/

namespace PrimePairConvolution

/-- An explicit error for the actual double-harmonic kernel, with the constant
constructed as the limit of the logarithmically weighted harmonic sums. -/
theorem doubleHarmonic_asymptotic_error (N : ℕ) (hN : 9 ≤ N) :
    |doubleHarmonic N -
      (Real.log (N : ℝ)^2 / 2 +
        2 * Real.eulerMascheroniConstant * Real.log (N : ℝ) +
        Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)| ≤
      3 / (Nat.sqrt N : ℝ)^2 + 2 * Real.log (N : ℝ) / Nat.sqrt N +
        4 * (Nat.sqrt N : ℝ) / N := by
  let m := Nat.sqrt N
  have hm3 : 3 ≤ m := Nat.le_sqrt.mpr hN
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmN : (m : ℝ)^2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  have hNm : (N : ℝ) < ((m : ℝ) + 1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  let L := Real.log (N : ℝ)
  let l := Real.log (m : ℝ)
  let a := (m : ℝ)⁻¹
  let e := (harmonic m : ℝ) - l - Real.eulerMascheroniConstant
  let s := (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
    l^2 / 2 - firstStieltjesConstant
  have ha0 : 0 ≤ a := inv_nonneg.mpr hmR.le
  have hl0 : 0 ≤ l := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ m by omega))
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hloglower : 2 * l ≤ L := by
    have h := Real.log_le_log (sq_pos_of_pos hmR) hmN
    simpa only [Real.log_pow, Nat.cast_ofNat, L, l] using h
  have hlogupper : L ≤ 2 * Real.log ((m : ℝ) + 1) := by
    have h := Real.log_le_log hNR hNm.le
    simpa only [Real.log_pow, Nat.cast_ofNat, L] using h
  have hgap : Real.log ((m : ℝ) + 1) - l ≤ a := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < (m : ℝ) + 1) hmR)
    rw [Real.log_div (by positivity) hmR.ne'] at h
    have heq : ((m : ℝ) + 1) / m - 1 = a := by
      dsimp [a]
      field_simp [hmR.ne'] <;> ring
    simpa only [l, heq] using h
  have hu : (l - L / 2)^2 ≤ a^2 := by
    have hlo : 0 ≤ L / 2 - l := by linarith
    have hhi : L / 2 - l ≤ a := by linarith
    nlinarith [mul_nonneg hlo (by linarith : 0 ≤ a - (L / 2 - l))]
  have he0 : 0 ≤ e := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
    simp only [Real.eulerMascheroniSeq', hm0.ne', if_false] at h
    dsimp [e, l]
    linarith
  have hea : e ≤ a := by
    have h := (abs_le.mp (harmonic_interval_error m hm0 (m : ℝ)
      le_rfl (by linarith))).2
    simpa only [e, l, a, one_div] using h
  have he2 : e^2 ≤ a^2 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr hea)]
  have hs := logWeightedHarmonic_error m hm3
  change 0 ≤ s ∧ s ≤ l / (m : ℝ) at hs
  have hsa : s ≤ l * a := by simpa only [div_eq_mul_inv, a] using hs.2
  have hLl : 0 ≤ L - l := by linarith
  have hcross : 2 * (L - l) * e ≤ 2 * (L - l) * a :=
    mul_le_mul_of_nonneg_left hea (by positivity)
  have hcross0 : 0 ≤ 2 * (L - l) * e := by positivity
  have hLa : l * a ≤ L * a := mul_le_mul_of_nonneg_right (by linarith) ha0
  have hcenter :
      |(2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
          2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
          (harmonic m : ℝ)^2) -
        (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
          Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)| ≤
      3 * a^2 + 2 * L * a := by
    have heq :
        (2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
            2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
            (harmonic m : ℝ)^2) -
          (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
            Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant) =
        -2 * (l - L / 2)^2 + 2 * (L - l) * e - e^2 - 2 * s := by
      dsimp [e, s]
      ring
    rw [heq]
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg e, sq_nonneg (l - L / 2)]
    · have hla0 : 0 ≤ l * a := mul_nonneg hl0 ha0
      nlinarith [sq_nonneg e, sq_nonneg (l - L / 2), sq_nonneg a]
  have hfinite := doubleHarmonic_finite_center_error N (by omega)
  have htri := (abs_sub_le (doubleHarmonic N)
    (2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
      2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
      (harmonic m : ℝ)^2)
    (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
      Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)).trans
    (add_le_add hfinite hcenter)
  simpa only [L, a, m, div_eq_mul_inv, inv_pow,
    add_comm, add_left_comm, add_assoc] using htri

end PrimePairConvolution


/-- One common constant for the limit and both quantitative estimates. -/
theorem solution :
    ∃ c : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
            Real.log (n : ℝ)^2 / 2)
        Filter.atTop (𝓝 c) ∧
      (∀ n : ℕ, 3 ≤ n →
        0 ≤ (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
          Real.log (n : ℝ)^2 / 2 - c ∧
        (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
          Real.log (n : ℝ)^2 / 2 - c ≤ Real.log (n : ℝ) / (n : ℝ)) ∧
      (∀ N : ℕ, 9 ≤ N →
        |(∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ)) -
          (Real.log (N : ℝ)^2 / 2 +
            2 * Real.eulerMascheroniConstant * Real.log (N : ℝ) +
            Real.eulerMascheroniConstant^2 - 2 * c)| ≤
          3 / (Nat.sqrt N : ℝ)^2 +
            2 * Real.log (N : ℝ) / (Nat.sqrt N : ℝ) +
            4 * (Nat.sqrt N : ℝ) / (N : ℝ)) := by
  refine ⟨PrimePairConvolution.firstStieltjesConstant, ?_, ?_, ?_⟩
  · have hc := PrimePairConvolution.tendsto_firstStieltjesSeq
    change Filter.Tendsto
      (fun n : ℕ => PrimePairConvolution.logWeightedHarmonic n -
        Real.log (n : ℝ)^2 / 2)
      Filter.atTop (𝓝 PrimePairConvolution.firstStieltjesConstant) at hc
    simpa only [PrimePairConvolution.logWeightedHarmonic_eq_sum_Icc] using hc
  · intro n hn
    exact PrimePairConvolution.logWeightedHarmonic_error n hn
  · intro N hN
    simpa only [PrimePairConvolution.doubleHarmonic] using
      PrimePairConvolution.doubleHarmonic_asymptotic_error N hN

#print axioms solution
