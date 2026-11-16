-- Prove2me | solution 2 for RGMISFast.binomial_moment_exponential_tail
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T04:00:48.934344+00:00
-- url     : https://prove2.me/submissions/67c83dde-b36f-4aa3-8429-1f4edc792325

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BinomialMomentTail
lemma choose_lower (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n:ℝ)/(k:ℝ))^k ≤ (n.choose k : ℝ) := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hzero : k = 0
      · subst k; simp
      have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1 : (0:ℝ) < k+1 := by positivity
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
      have hratio : ((n:ℝ)+1)/((k:ℝ)+1) ≤ (n:ℝ)/(k:ℝ) := by
        apply (div_le_div_iff₀ hk1 hkpos).mpr
        have hh : (k:ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
        nlinarith
      have hh := ih n (by omega) (by omega)
      have hp := (pow_le_pow_left₀ (by positivity : 0 ≤ ((n:ℝ)+1)/((k:ℝ)+1)) hratio k).trans hh
      have he : ((n:ℝ)+1)*(n.choose k:ℝ) = ((n+1).choose (k+1):ℝ)*((k:ℝ)+1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n k
      simp only [Nat.cast_add,Nat.cast_one,pow_succ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hk1).mpr
      rw [← he]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (n:ℝ)+1)
end BinomialMomentTail
open BinomialMomentTail
 theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Measurable (fun ω => (K ω).choose k) ∧
      ∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k))
    (x : ℝ) (hx : 1 ≤ x) :
    μ {ω | 32*C*x < (K ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let k := ⌊x⌋₊+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hxk : x < (k:ℝ) := by simpa [k] using Nat.lt_floor_add_one x
  have hkx : (k:ℝ) ≤ 2*x := by
    have hh := Nat.floor_le (show 0 ≤ x by linarith)
    dsimp [k]; push_cast; linarith
  have hCp : 0 < C := by linarith
  have hsub : {ω | 32*C*x < (K ω:ℝ)} ⊆
      {ω | ENNReal.ofReal ((16*C)^k) ≤ ((K ω).choose k : ℝ≥0∞)} := by
    intro ω hω
    change 32*C*x < (K ω:ℝ) at hω
    have hscale : 16*C*(k:ℝ) < (K ω:ℝ) := by nlinarith
    have hkn : k ≤ K ω := by
      have : (k:ℝ) ≤ K ω := by nlinarith
      exact_mod_cast this
    have hh := choose_lower (K ω) k hk hkn
    have hratio : 16*C ≤ (K ω:ℝ)/(k:ℝ) := (le_div_iff₀ hkpos).mpr hscale.le
    have hb := (pow_le_pow_left₀ (by positivity : 0 ≤ 16*C) hratio k).trans hh
    simpa using ENNReal.ofReal_le_ofReal hb
  have hm : Measurable (fun ω => ((K ω).choose k : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (hmom k hk).1
  have he : Real.exp 1/8 ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have h := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ μ {ω | ENNReal.ofReal ((16*C)^k) ≤ ((K ω).choose k : ℝ≥0∞)} := measure_mono hsub
    _ ≤ (∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ) / ENNReal.ofReal ((16*C)^k) :=
      meas_ge_le_lintegral_div hm.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k) / ENNReal.ofReal ((16*C)^k) :=
      ENNReal.div_le_div_right (hmom k hk).2 _
    _ = ENNReal.ofReal ((Real.exp 1/8)^k) := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity), ← div_pow]
      congr 2
      field_simp
      <;> ring
    _ ≤ ENNReal.ofReal ((Real.exp (-1))^k) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) he k)
    _ = ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
#print axioms solution
