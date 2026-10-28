-- Prove2me | solution 1 for SLPEPricing.Regret.hoeffding_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:26:44.564644+00:00
-- url     : https://prove2.me/submissions/9252d27f-8ea7-4b88-8f84-a5fd60ab8754

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (σsq : ℝ≥0)
    (hindep : iIndepFun X P) (hsub : ∀ j, HasSubgaussianMGF (X j) σsq P)
    (hσ : (σsq : ℝ) ≤ 1 / 3)
    (ρ Δ : ℝ) (hρ : 0 < ρ) (hΔ : 0 < Δ) (T : ℕ) (hT : 2 ≤ T)
    (hnT : 2 * ρ ^ 4 * Real.log (T : ℝ) / Δ ^ 4 ≤ (n : ℝ)) :
    P.real {ω | Δ ^ 2 / ρ ^ 2 < |(∑ j, X j ω) / (n : ℝ)|} ≤ 1 / (T : ℝ) ^ 2 := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ≥0, (c' : ℝ) = 1 / 3 := ⟨⟨1 / 3, by norm_num⟩, rfl⟩
  have hsub' : ∀ j, HasSubgaussianMGF (X j) c' P := fun j =>
    ⟨(hsub j).integrable_exp_mul, fun t => ((hsub j).mgf_le t).trans
      (Real.exp_le_exp.mpr (by rw [hc']; gcongr))⟩
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep (c := fun _ => c')
    (s := Finset.univ) (fun i _ => hsub' i)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  set ε := Δ ^ 2 / ρ ^ 2 with hε
  have hε0 : 0 ≤ (n : ℝ) * ε := by positivity
  have h1 := hsum.measure_ge_le hε0
  have h2 := hsum.neg.measure_ge_le hε0
  have hcs : ((∑ _i : Fin n, c' : ℝ≥0) : ℝ) = n * (1 / 3) := by
    rw [NNReal.coe_sum]
    simp [hc']
  rw [hcs] at h1 h2
  set L := Real.log (T : ℝ) with hL
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have hA : 2 * ρ ^ 4 * L ≤ n * Δ ^ 4 := by
    rw [div_le_iff₀ (by positivity)] at hnT; linarith
  have hB : 2 * L ≤ n * ε ^ 2 := by
    have : (n : ℝ) * ε ^ 2 = (n * Δ ^ 4) / ρ ^ 4 := by
      rw [hε]; field_simp <;> ring
    rw [this, le_div_iff₀ hρ4]; linarith
  have hC : 3 * L ≤ ((n : ℝ) * ε) ^ 2 / (2 * (n * (1 / 3))) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : Real.exp (-(((n : ℝ) * ε) ^ 2) / (2 * (n * (1 / 3)))) ≤ 1 / (T : ℝ) ^ 3 := by
    have hT3 : Real.exp (3 * L) = (T : ℝ) ^ 3 := by
      rw [hL, show (3 : ℝ) * Real.log (T : ℝ) = Real.log ((T : ℝ) ^ 3) by norm_num [Real.log_pow],
        Real.exp_log (by positivity)]
    rw [neg_div, Real.exp_neg, ← hT3, one_div (Real.exp (3 * L))]
    exact inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.mpr hC)
  have hsub_set : {ω | ε < |(∑ j, X j ω) / (n : ℝ)|} ⊆
      {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, X i ω} ∪
      {ω | (n : ℝ) * ε ≤ (-fun ω => ∑ i ∈ Finset.univ, X i ω) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [abs_div, abs_of_pos hn0, lt_div_iff₀ hn0, lt_abs] at hω
    rcases hω with h | h
    · left; simp only [Set.mem_setOf_eq]; linarith
    · right; simp only [Set.mem_setOf_eq, Pi.neg_apply]; linarith
  calc P.real {ω | ε < |(∑ j, X j ω) / (n : ℝ)|}
      ≤ P.real ({ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.univ, X i ω} ∪
      {ω | (n : ℝ) * ε ≤ (-fun ω => ∑ i ∈ Finset.univ, X i ω) ω}) := measureReal_mono hsub_set
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 1 / (T : ℝ) ^ 3 + 1 / (T : ℝ) ^ 3 := add_le_add (h1.trans hE) (h2.trans hE)
    _ ≤ 1 / (T : ℝ) ^ 2 := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (show (0:ℝ) < T by linarith) 2]
