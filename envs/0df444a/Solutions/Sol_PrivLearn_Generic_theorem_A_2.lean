-- Prove2me | solution 1 for PrivLearn.Generic.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:01:30.852352+00:00
-- url     : https://prove2.me/submissions/7de58778-c950-41e0-9b04-6e173db04e16

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i j, IdentDistrib (X i) (X j) P P)
    (μ a b : ℝ) (hmean : ∀ i, ∫ ω, X i ω ∂P = μ) (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b)
    (δ : ℝ) (hδ : 0 < δ) :
    P {ω | δ ≤ |(∑ i, X i ω) / n - μ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2)) := by
  classical
  have hone : P {ω | δ ≤ |(∑ i, X i ω) / n - μ|} ≤ 1 := prob_le_one
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine hone.trans ?_
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    rw [show (2:ℝ) = ((2:ℝ≥0):ℝ) by simp, ENNReal.ofReal_coe_nnreal]
    norm_num
  by_cases hab : (b - a) ^ 2 = 0
  · refine hone.trans ?_
    rw [hab]
    simp only [div_zero, Real.exp_zero, mul_one]
    rw [show (2:ℝ) = ((2:ℝ≥0):ℝ) by simp, ENNReal.ofReal_coe_nnreal]
    norm_num
  have hab' : 0 < (b - a) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hab)
  set c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2 with hc
  have hcR : (c : ℝ) = (b - a) ^ 2 / 4 := by
    rw [hc]
    push_cast
    rw [div_pow, Real.norm_eq_abs, sq_abs]
    norm_num
  have hY : ∀ i, HasSubgaussianMGF (fun ω => X i ω - μ) c P := by
    intro i
    have := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := X i) (a := a) (b := b)
      (hmeas i).aemeasurable (ae_of_all _ (hbdd i))
    have h2 : P[X i] = μ := hmean i
    simpa [h2] using this
  have hYn : ∀ i, HasSubgaussianMGF (fun ω => -(X i ω - μ)) c P := fun i => (hY i).neg
  have hind1 : iIndepFun (fun i ω => X i ω - μ) P :=
    hindep.comp (fun _ x => x - μ) (fun _ => measurable_id.sub_const _)
  have hind2 : iIndepFun (fun i ω => -(X i ω - μ)) P :=
    hindep.comp (fun _ x => -(x - μ)) (fun _ => (measurable_id.sub_const _).neg)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hε : 0 ≤ (n:ℝ) * δ := by positivity
  have hsum : ∑ _i : Fin n, c = n * c := by simp
  have key : ∀ (Z : Fin n → Ω → ℝ), iIndepFun Z P → (∀ i, HasSubgaussianMGF (Z i) c P) →
      P.real {ω | (n:ℝ) * δ ≤ ∑ i, Z i ω} ≤ Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2) := by
    intro Z hZ hZs
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ) (c := fun _ => c) hZ
      (fun i _ => hZs i) hε
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast, hcR]
    field_simp
    ring
  have h1 := key _ hind1 hY
  have h2 := key _ hind2 hYn
  have hsub : {ω | δ ≤ |(∑ i, X i ω) / n - μ|} ⊆
      {ω | (n:ℝ) * δ ≤ ∑ i, (X i ω - μ)} ∪ {ω | (n:ℝ) * δ ≤ ∑ i, -(X i ω - μ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e : ∑ i, (X i ω - μ) = ∑ i, X i ω - n * μ := by
      simp [Finset.sum_sub_distrib]
    have e2 : ∑ i, -(X i ω - μ) = -(∑ i, (X i ω - μ)) := by simp
    rw [e2, e]
    have e3 : (∑ i, X i ω) / n - μ = (∑ i, X i ω - n * μ) / n := by
      field_simp
    rw [e3, abs_div, abs_of_pos hnpos, le_div_iff₀ hnpos] at hω
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; linarith
  calc P {ω | δ ≤ |(∑ i, X i ω) / n - μ|}
      ≤ P ({ω | (n:ℝ) * δ ≤ ∑ i, (X i ω - μ)} ∪ {ω | (n:ℝ) * δ ≤ ∑ i, -(X i ω - μ)}) :=
        measure_mono hsub
    _ ≤ P {ω | (n:ℝ) * δ ≤ ∑ i, (X i ω - μ)} + P {ω | (n:ℝ) * δ ≤ ∑ i, -(X i ω - μ)} :=
        measure_union_le _ _
    _ = ENNReal.ofReal (P.real {ω | (n:ℝ) * δ ≤ ∑ i, (X i ω - μ)}) +
        ENNReal.ofReal (P.real {ω | (n:ℝ) * δ ≤ ∑ i, -(X i ω - μ)}) := by
        rw [Measure.real, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2)) +
        ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2)) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1; ring
