-- Prove2me | solution 1 for RGMISFast.binomial_moment_exponential_tail
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:02:46.952076+00:00
-- url     : https://prove2.me/submissions/99b834e9-e45d-4ac4-8760-f4e815b175b6

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.binomial_moment_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Measurable (fun ω => (K ω).choose k) ∧
      ∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k))
    (x : ℝ) (hx : 1 ≤ x) :
    μ {ω | 32*C*x < (K ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  set k : ℕ := ⌈x⌉₊ with hkdef
  have hxk : x ≤ k := Nat.le_ceil x
  have hk1 : 1 ≤ k := by
    have : (1:ℝ) ≤ k := le_trans hx hxk
    exact_mod_cast this
  have hkx : (k:ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk2x : (k:ℝ) ≤ 2 * x := by linarith
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk1
  -- lower bound on binomial coefficient
  have hlow : ∀ n : ℕ, 32*C*x < (n:ℝ) → (15*C)^k ≤ ((n.choose k : ℕ) : ℝ) := by
    intro n hn
    have hkn : k ≤ n := by
      have : (k:ℝ) ≤ n := by nlinarith
      exact_mod_cast this
    have h1 := Nat.pow_le_choose (α := ℝ) k n
    have hfac : ((k.factorial : ℕ) : ℝ) ≤ (k:ℝ)^k := by
      exact_mod_cast Nat.factorial_le_pow k
    have hcast : (((n + 1 - k : ℕ)) : ℝ) = (n:ℝ) + 1 - k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at h1
    have hbig : 15 * C * k ≤ (n:ℝ) + 1 - k := by nlinarith
    have hfacpos : (0:ℝ) < (k.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos k
    calc (15*C)^k = (15*C*k)^k / (k:ℝ)^k := by
          rw [mul_pow (15*C), mul_div_assoc, div_self (by positivity), mul_one]
      _ ≤ ((n:ℝ) + 1 - k)^k / (k:ℝ)^k := by
          gcongr
      _ ≤ ((n:ℝ) + 1 - k)^k / ((k.factorial : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_left (by have : (0:ℝ) ≤ 15*C*k := by positivity
                                              exact pow_nonneg (by linarith) _) hfacpos hfac
      _ ≤ _ := h1
  obtain ⟨hmeas, hint⟩ := hmom k hk1
  set f : Ω → ℝ≥0∞ := fun ω => ((K ω).choose k : ℝ≥0∞)
  have hf : Measurable f := by
    exact (measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0∞))).comp hmeas
  set ε : ℝ≥0∞ := ENNReal.ofReal ((15*C)^k)
  have hsub : {ω | 32*C*x < (K ω:ℝ)} ⊆ {ω | ε ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have := hlow (K ω) hω
    simp only [ε, f]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal this
  have hmarkov := mul_meas_ge_le_lintegral₀ hf.aemeasurable ε (μ := μ)
  have hεpos : ε ≠ 0 := by
    simp only [ε]; rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hεtop : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : μ {ω | ε ≤ f ω} ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k) / ε := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεpos) (Or.inl hεtop), mul_comm]
    exact hmarkov.trans hint
  have hratio : ENNReal.ofReal ((2*Real.exp 1*C)^k) / ε = ENNReal.ofReal ((2*Real.exp 1/15)^k) := by
    simp only [ε]
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [← div_pow]; congr 1; field_simp
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : 2*Real.exp 1/15 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, div_le_iff₀ (by norm_num), ← div_eq_inv_mul]
    rw [le_div_iff₀ he0]
    nlinarith
  have hfinal : (2*Real.exp 1/15)^k ≤ Real.exp (-x) := by
    calc (2*Real.exp 1/15)^k ≤ (Real.exp (-1))^k := by
          apply pow_le_pow_left₀ (by positivity) hbase
      _ = Real.exp (-(k:ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  calc μ {ω | 32*C*x < (K ω:ℝ)} ≤ μ {ω | ε ≤ f ω} := measure_mono hsub
    _ ≤ _ := hstep
    _ = _ := hratio
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Measurable (fun ω => (K ω).choose k) ∧
      ∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k))
    (x : ℝ) (hx : 1 ≤ x) :
    μ {ω | 32*C*x < (K ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) :=
  RGMISFast.binomial_moment_exponential_tail μ K C hC hmom x hx
