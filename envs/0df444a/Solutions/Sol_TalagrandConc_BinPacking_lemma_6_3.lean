-- Prove2me | solution 1 for TalagrandConc.BinPacking.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:33:08.403078+00:00
-- url     : https://prove2.me/submissions/a705a23f-64fa-443b-91cd-8b7504b4088c

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.BinPacking

/-- `exp t ≤ 1 + (e - 1) t` on `[0, 1]`. -/
lemma exp_le_linear {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp t ≤ 1 + (Real.exp 1 - 1) * t := by
  have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (sub_nonneg.2 h1) h0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at this
  linarith

lemma secondMoment_nonneg (μ : Measure unitInterval) : 0 ≤ secondMoment μ :=
  integral_nonneg (fun ω => sq_nonneg _)

lemma integrable_of_continuous_unit (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (f : unitInterval → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- `∫ exp(ω²) dμ ≤ exp((e-1) E X²)`. -/
lemma integral_exp_sq_le (μ : Measure unitInterval) [IsProbabilityMeasure μ] :
    ∫ ω, Real.exp ((ω : ℝ) ^ 2) ∂μ ≤ Real.exp ((Real.exp 1 - 1) * secondMoment μ) := by
  have hc1 : Continuous (fun ω : unitInterval => Real.exp ((ω : ℝ) ^ 2)) := by fun_prop
  have hc2 : Continuous (fun ω : unitInterval => 1 + (Real.exp 1 - 1) * (ω : ℝ) ^ 2) := by
    fun_prop
  have hc3 : Continuous (fun ω : unitInterval => (ω : ℝ) ^ 2) := by fun_prop
  have h1 : ∫ ω, Real.exp ((ω : ℝ) ^ 2) ∂μ ≤ ∫ ω, (1 + (Real.exp 1 - 1) * (ω : ℝ) ^ 2) ∂μ := by
    apply integral_mono (integrable_of_continuous_unit μ _ hc1)
      (integrable_of_continuous_unit μ _ hc2)
    intro ω
    have h0 : 0 ≤ (ω : ℝ) := ω.2.1
    have h1 : (ω : ℝ) ≤ 1 := ω.2.2
    exact exp_le_linear (sq_nonneg _) (by nlinarith)
  have h2 : ∫ ω, (1 + (Real.exp 1 - 1) * (ω : ℝ) ^ 2) ∂μ = 1 + (Real.exp 1 - 1) * secondMoment μ := by
    rw [integral_add (integrable_const _) ((integrable_of_continuous_unit μ _ hc3).const_mul _),
      integral_const, integral_const_mul]
    simp [secondMoment]
  have h3 := Real.add_one_le_exp ((Real.exp 1 - 1) * secondMoment μ)
  linarith

/-- Talagrand (1995), Lemma 6.3. -/
theorem lemma_6_3_core (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ)
        {x | 2 * Real.sqrt N * Real.sqrt (secondMoment μ) ≤ l2Norm x} ≤
      ENNReal.ofReal (Real.exp (-(2 * N * secondMoment μ))) := by
  set m := secondMoment μ with hm
  have hm0 : 0 ≤ m := secondMoment_nonneg μ
  set P := Measure.pi (fun _ : Fin N => μ) with hP
  -- the test function
  set g : (Fin N → unitInterval) → ℝ := fun x => ∏ i, Real.exp ((x i : ℝ) ^ 2) with hg
  have hg_cont : Continuous g := by
    rw [hg]; fun_prop
  have hg_nn : ∀ x, 0 ≤ g x := fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
  have hg_int : Integrable g P :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  -- its integral
  have hgint : ∫ x, g x ∂P = (∫ ω, Real.exp ((ω : ℝ) ^ 2) ∂μ) ^ N := by
    rw [hg, hP]
    have := integral_fintype_prod_eq_pow (ι := Fin N) (fun ω : unitInterval => Real.exp ((ω : ℝ) ^ 2))
      (μ := μ)
    rw [this, Fintype.card_fin]
  have hgle : ∫ x, g x ∂P ≤ Real.exp ((Real.exp 1 - 1) * N * m) := by
    rw [hgint]
    calc (∫ ω, Real.exp ((ω : ℝ) ^ 2) ∂μ) ^ N ≤ (Real.exp ((Real.exp 1 - 1) * m)) ^ N :=
          pow_le_pow_left₀ (integral_nonneg (fun ω => (Real.exp_pos _).le))
            (integral_exp_sq_le μ) N
      _ = Real.exp ((Real.exp 1 - 1) * N * m) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  -- lintegral form
  have hlint : ∫⁻ x, ENNReal.ofReal (g x) ∂P ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * N * m)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nn)]
    exact ENNReal.ofReal_le_ofReal hgle
  -- Markov
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (4 * N * m)) with hε
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hεtop : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov : ε * P {x | ε ≤ ENNReal.ofReal (g x)} ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂P :=
    mul_meas_ge_le_lintegral₀ (ENNReal.measurable_ofReal.comp hg_cont.measurable).aemeasurable ε
  -- set inclusion
  have hsub : {x : Fin N → unitInterval | 2 * Real.sqrt N * Real.sqrt m ≤ l2Norm x} ⊆
      {x | ε ≤ ENNReal.ofReal (g x)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hε]
    apply ENNReal.ofReal_le_ofReal
    have hsum0 : 0 ≤ ∑ i, (x i : ℝ) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4 : 4 * N * m ≤ ∑ i, (x i : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hx 2
      unfold l2Norm at hsq
      rw [Real.sq_sqrt hsum0] at hsq
      have e : (2 * Real.sqrt N * Real.sqrt m) ^ 2 = 4 * N * m := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hm0]; ring
      linarith
    rw [hg]
    simp only
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr h4
  calc P {x | 2 * Real.sqrt N * Real.sqrt m ≤ l2Norm x}
      ≤ P {x | ε ≤ ENNReal.ofReal (g x)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * N * m)) / ε := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop), mul_comm]
        exact hmarkov.trans hlint
    _ = ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * N * m) / Real.exp (4 * N * m)) := by
        rw [hε, ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * N * m))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        have he : Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; norm_num at this; linarith
        have hNm : 0 ≤ (N : ℝ) * m := mul_nonneg (Nat.cast_nonneg N) hm0
        nlinarith

end TalagrandConc.BinPacking

open TalagrandConc.BinPacking


theorem solution (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ)
        {x | 2 * Real.sqrt N * Real.sqrt (secondMoment μ) ≤ l2Norm x} ≤
      ENNReal.ofReal (Real.exp (-(2 * N * secondMoment μ))) := by
  exact lemma_6_3_core μ N
