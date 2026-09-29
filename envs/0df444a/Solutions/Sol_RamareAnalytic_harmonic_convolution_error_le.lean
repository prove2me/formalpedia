-- Prove2me | solution 1 for RamareAnalytic.harmonic_convolution_error_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:46:27.249207+00:00
-- url     : https://prove2.me/submissions/3d2846ae-ec65-4611-8da7-cae66e2d8a04

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Order.Floor.Semifield

set_option autoImplicit false

namespace RamareAnalytic

/-!
An elementary uniform harmonic remainder for the proposed Ramaré large-range
argument. This is a new choice of explicit constants in the source's harmonic
convolution method (Ramaré 1995, Lemmas 3.2--3.3, printed pp.656--658).
It assumes no prime estimate and no squarefree/totient estimate.
-/

private theorem two_fifths_rpow_le_linear (x : ℝ) (hx : 2 ≤ x) :
    (x + 1) ^ (2 / 5 : ℝ) ≤ (4 / 5 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have hlin : x + 1 ≤ (3 / 2 : ℝ) * x := by linarith
  have hsq : (x + 1) ^ 2 ≤ ((3 / 2 : ℝ) * x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlin 2
  have hcube : (2 : ℝ) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hx 3
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hprod := mul_nonneg (sub_nonneg.mpr hcube) hx2
  have hpoly : (x + 1) ^ 2 ≤ ((4 / 5 : ℝ) * x) ^ 5 := by
    nlinarith
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 5)).mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num only [show (2 / 5 : ℝ) * 5 = 2 by norm_num,
    Real.rpow_ofNat]
  exact hpoly

private theorem log_two_le_three_quarters :
    Real.log 2 ≤ (3 / 4 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 0
  norm_num at h
  linarith

/-- The gamma sandwiches yield a uniform bound throughout one floor interval. -/
private theorem harmonic_error_le_inverse (n : ℕ) (hn : 0 < n)
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
  have hgap :
      Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < (n : ℝ) + 1) hnR)
    rw [Real.log_div (by positivity) hnR.ne'] at h
    have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp [hnR.ne'] <;> ring
    rwa [heq] at h
  apply abs_le.mpr
  constructor <;> linarith

/-- The case t ≥ 1, including noninteger arguments. -/
theorem harmonic_floor_error_le_of_one_le (t : ℝ) (ht : 1 ≤ t) :
    |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
      (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hn : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
  have htn : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hp : 0 < t ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos ht0 _
  by_cases hn1 : ⌊t⌋₊ = 1
  · have ht2 : t < 2 := by norm_num [hn1] at htn; exact htn
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
    have hlog2 : Real.log t ≤ Real.log 2 := Real.log_le_log ht0 ht2.le
    have hglo := Real.one_half_lt_eulerMascheroniConstant
    have hghi := Real.eulerMascheroniConstant_lt_two_thirds
    have herr :
        |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
          (1 / 2 : ℝ) := by
      norm_num [hn1, harmonic]
      apply abs_le.mpr
      constructor <;> linarith [log_two_le_three_quarters]
    have hpow : t ^ (2 / 5 : ℝ) ≤ (8 / 5 : ℝ) := by
      calc
        t ^ (2 / 5 : ℝ) ≤ (2 + 1 : ℝ) ^ (2 / 5 : ℝ) :=
          Real.rpow_le_rpow ht0.le (by linarith) (by norm_num)
        _ ≤ (4 / 5 : ℝ) * 2 := two_fifths_rpow_le_linear 2 (by norm_num)
        _ = 8 / 5 := by norm_num
    have hhalf : (1 / 2 : ℝ) ≤ (4 / 5 : ℝ) / t ^ (2 / 5 : ℝ) :=
      (le_div_iff₀ hp).mpr (by nlinarith)
    calc
      _ ≤ (1 / 2 : ℝ) := herr
      _ ≤ (4 / 5 : ℝ) / t ^ (2 / 5 : ℝ) := hhalf
      _ = (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by
        rw [Real.rpow_neg ht0.le]
        rfl
  · have hn2 : 2 ≤ ⌊t⌋₊ := by omega
    have hnR : 0 < (⌊t⌋₊ : ℝ) := by exact_mod_cast hn
    have hn2R : (2 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hn2
    have hpow :
        t ^ (2 / 5 : ℝ) ≤ (4 / 5 : ℝ) * (⌊t⌋₊ : ℝ) := by
      calc
        t ^ (2 / 5 : ℝ) ≤ ((⌊t⌋₊ : ℝ) + 1) ^ (2 / 5 : ℝ) :=
          Real.rpow_le_rpow ht0.le htn.le (by norm_num)
        _ ≤ (4 / 5 : ℝ) * (⌊t⌋₊ : ℝ) :=
          two_fifths_rpow_le_linear (⌊t⌋₊ : ℝ) hn2R
    have hinv :
        1 / (⌊t⌋₊ : ℝ) ≤ (4 / 5 : ℝ) / t ^ (2 / 5 : ℝ) :=
      (div_le_div_iff₀ hnR hp).mpr (by simpa using hpow)
    calc
      _ ≤ 1 / (⌊t⌋₊ : ℝ) := harmonic_error_le_inverse ⌊t⌋₊ hn t hnt htn
      _ ≤ (4 / 5 : ℝ) / t ^ (2 / 5 : ℝ) := hinv
      _ = (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by
        rw [Real.rpow_neg ht0.le]
        rfl

private theorem exp_neg_six_fifths_le :
    Real.exp (-(6 / 5 : ℝ)) ≤ (8 / 25 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) 4
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at hs
  have hmul := mul_le_mul_of_nonneg_left hs
    (Real.exp_pos (-(6 / 5 : ℝ))).le
  have hcancel : Real.exp (-(6 / 5 : ℝ)) * Real.exp (6 / 5 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hcancel] at hmul
  nlinarith

/-- A global bound for the positive part of -log t - γ. -/
private theorem neg_log_sub_gamma_le (t : ℝ) (ht : 0 < t) :
    -Real.log t - Real.eulerMascheroniConstant ≤
      (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hc :
      Real.exp (-1 - (2 / 5 : ℝ) * Real.eulerMascheroniConstant) ≤
        (8 / 25 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr (show
      -1 - (2 / 5 : ℝ) * Real.eulerMascheroniConstant ≤ -(6 / 5 : ℝ) by linarith))
    exact exp_neg_six_fifths_le
  have h := Real.add_one_le_exp
    (-(2 / 5 : ℝ) * (Real.log t + Real.eulerMascheroniConstant) - 1)
  have heq :
      Real.exp (-(2 / 5 : ℝ) *
          (Real.log t + Real.eulerMascheroniConstant) - 1) =
        Real.exp (-1 - (2 / 5 : ℝ) * Real.eulerMascheroniConstant) *
          t ^ (-(2 / 5 : ℝ)) := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  have hmul := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg ht.le (-(2 / 5 : ℝ)))
  linarith

/-- Uniform in every positive real argument, so usable after convolution at t/d. -/
theorem harmonic_floor_error_le (t : ℝ) (ht : 0 < t) :
    |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
      (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by
  by_cases ht1 : 1 ≤ t
  · exact harmonic_floor_error_le_of_one_le t ht1
  · have htlt : t < 1 := lt_of_not_ge ht1
    have hfloor : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr htlt
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le htlt.le
    have hpow : 1 ≤ t ^ (-(2 / 5 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htlt.le (by norm_num)
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hupper := neg_log_sub_gamma_le t ht
    simp only [hfloor, harmonic_zero, Rat.cast_zero, zero_sub]
    apply abs_le.mpr
    constructor
    · linarith
    · exact hupper

end RamareAnalytic
set_option autoImplicit false

open scoped BigOperators

namespace RamareAnalytic

/-!
A finite-to-infinite error transfer for harmonic convolution. The sequence is
defined on natural numbers with h(0)=0, the explicit extension of a sequence
on positive integers. The coefficient moment assumptions below have not yet
been proved for Ramaré's correction sequence.

The parameter hH is exactly the independently verified harmonic_floor_error_le
interface. This file does not import a temporary local module or assume the
convolution estimate that it derives.
-/

noncomputable def harmonicConvolution (h : ℕ → ℝ) (N : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * (harmonic ⌊N / (d : ℝ)⌋₊ : ℝ)

/-- Terms beyond the natural floor cutoff vanish, including the zero index. -/
theorem harmonicConvolution_eq_tsum (h : ℕ → ℝ) (N : ℝ) :
    harmonicConvolution h N =
      ∑' d : ℕ, h d * (harmonic ⌊N / (d : ℝ)⌋₊ : ℝ) := by
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
    simp [hz]

/-- At an integer cutoff, the harmonic index is ordinary natural division. -/
theorem harmonicConvolution_nat (h : ℕ → ℝ) (N : ℕ) :
    harmonicConvolution h N =
      ∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ) := by
  simp only [harmonicConvolution, Nat.floor_natCast, Nat.floor_div_eq_div]

/--
Mass, logarithmic moment, and weighted absolute moment transfer the uniform
harmonic remainder to a finite convolution. No moment identity is hidden in
a definition, and the logarithmic moment appears with its actual sign.
-/
theorem harmonicConvolution_error_le
    (hH : ∀ (t : ℝ), 0 < t →
      |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
        (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)))
    (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hmass : HasSum h 1)
    (hlog : Summable (fun d : ℕ => h d * Real.log (d : ℝ)))
    (hweight : Summable (fun d : ℕ => |h d| * (d : ℝ) ^ (2 / 5 : ℝ)))
    (N : ℝ) (hN : 0 < N) :
    |harmonicConvolution h N -
        (Real.log N + Real.eulerMascheroniConstant -
          ∑' d : ℕ, h d * Real.log (d : ℝ))| ≤
      (4 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) *
        ∑' d : ℕ, |h d| * (d : ℝ) ^ (2 / 5 : ℝ) := by
  let E : ℕ → ℝ := fun d => h d *
    ((harmonic ⌊N / (d : ℝ)⌋₊ : ℝ) -
      Real.log (N / (d : ℝ)) - Real.eulerMascheroniConstant)
  let C : ℝ := (4 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ))
  have hpoint : ∀ d : ℕ,
      ‖E d‖ ≤ C * (|h d| * (d : ℝ) ^ (2 / 5 : ℝ)) := by
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [E, h0]
    · have hdR : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hd0
      have hh := hH (N / (d : ℝ)) (div_pos hN hdR)
      have hpow : (N / (d : ℝ)) ^ (-(2 / 5 : ℝ)) =
          N ^ (-(2 / 5 : ℝ)) * (d : ℝ) ^ (2 / 5 : ℝ) := by
        rw [Real.div_rpow hN.le hdR.le, Real.rpow_neg hdR.le, div_inv_eq_mul]
      calc
        ‖E d‖ = |h d| *
            |(harmonic ⌊N / (d : ℝ)⌋₊ : ℝ) -
              Real.log (N / (d : ℝ)) - Real.eulerMascheroniConstant| := by
          dsimp only [E]
          rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |h d| * ((4 / 5 : ℝ) *
            (N / (d : ℝ)) ^ (-(2 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = C * (|h d| * (d : ℝ) ^ (2 / 5 : ℝ)) := by
          rw [hpow]
          dsimp [C]
          ring
  have hE : Summable E :=
    (hweight.mul_left C).of_norm_bounded hpoint
  have hbound : |∑' d : ℕ, E d| ≤
      C * ∑' d : ℕ, |h d| * (d : ℝ) ^ (2 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs] using
      hE.hasSum.norm_le_of_bounded (hweight.hasSum.mul_left C) hpoint
  have hdecomp :
      HasSum (fun d : ℕ => h d * (harmonic ⌊N / (d : ℝ)⌋₊ : ℝ))
        ((∑' d : ℕ, E d) + (Real.log N + Real.eulerMascheroniConstant) -
          ∑' d : ℕ, h d * Real.log (d : ℝ)) := by
    have hs := (hE.hasSum.add
      (hmass.mul_left (Real.log N + Real.eulerMascheroniConstant))).sub hlog.hasSum
    simp only [mul_one] at hs
    apply hs.congr_fun
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [E, h0]
    · have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
      dsimp [E]
      rw [Real.log_div hN.ne' hdR]
      ring
  have hcenter : harmonicConvolution h N -
        (Real.log N + Real.eulerMascheroniConstant -
          ∑' d : ℕ, h d * Real.log (d : ℝ)) = ∑' d : ℕ, E d := by
    rw [harmonicConvolution_eq_tsum, hdecomp.tsum_eq]
    ring
  rw [hcenter]
  exact hbound

/-- The form directly compatible with the finite arithmetic convolution. -/
theorem harmonicConvolution_error_le_nat
    (hH : ∀ (t : ℝ), 0 < t →
      |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
        (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)))
    (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hmass : HasSum h 1)
    (hlog : Summable (fun d : ℕ => h d * Real.log (d : ℝ)))
    (hweight : Summable (fun d : ℕ => |h d| * (d : ℝ) ^ (2 / 5 : ℝ)))
    (N : ℕ) (hN : 0 < N) :
    |(∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ)) -
        (Real.log (N : ℝ) + Real.eulerMascheroniConstant -
          ∑' d : ℕ, h d * Real.log (d : ℝ))| ≤
      (4 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ)) *
        ∑' d : ℕ, |h d| * (d : ℝ) ^ (2 / 5 : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  simpa only [harmonicConvolution_nat] using
    harmonicConvolution_error_le hH h h0 hmass hlog hweight (N : ℝ) hNR

end RamareAnalytic

theorem solution (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hmass : HasSum h 1)
    (hlog : Summable (fun d : ℕ => h d * Real.log (d : ℝ)))
    (hweight : Summable (fun d : ℕ => |h d| * (d : ℝ) ^ (2 / 5 : ℝ)))
    (N : ℝ) (hN : 0 < N) :
    |(∑ d ∈ Finset.Icc 1 ⌊N⌋₊,
        h d * (harmonic ⌊N / (d : ℝ)⌋₊ : ℝ)) -
        (Real.log N + Real.eulerMascheroniConstant -
          ∑' d : ℕ, h d * Real.log (d : ℝ))| ≤
      (4 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) *
        ∑' d : ℕ, |h d| * (d : ℝ) ^ (2 / 5 : ℝ) := by
  exact RamareAnalytic.harmonicConvolution_error_le
    RamareAnalytic.harmonic_floor_error_le h h0 hmass hlog hweight N hN

#print axioms solution
