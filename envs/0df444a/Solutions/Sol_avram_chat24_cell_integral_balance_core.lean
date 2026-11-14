-- Prove2me | solution 1 for avram_chat24_cell_integral_balance_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:29:28.576453+00:00
-- url     : https://prove2.me/submissions/04c2f3cc-acf9-4827-af2d-0a088a77d212

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (ν : Measure (ℝ≥0 × ℝ)) (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (u : ℕ → ℝ≥0) (N : ℕ) (V m e : ℕ → ℝ) (δ h : ℝ) (hh : 0 < h)
    (w : ℝ → ℝ)
    (hmass : ∀ i ∈ Finset.range N,
      let H : ℝ≥0 × ℝ → ℝ := fun p => if u i < p.1 ∧ p.1 ≤ u (i + 1) then -p.2 else 0
      Integrable H ν ∧ (∫ p, H p ∂ν) = m i)
    (hvol : ∀ i ∈ Finset.range N, μ (Ioc (u i) (u (i + 1))) = ENNReal.ofReal h) :
    (∑ i ∈ Finset.range N, e i * (w (V i + δ - m i) - w (V i))) =
      (∫ p, (∑ i ∈ Finset.range N,
        if u i < p.1 ∧ p.1 ≤ u (i + 1) then
          e i * ((w (V i - m i) - w (V i)) / m i) * (-p.2) else 0) ∂ν) +
      (∫ t, (∑ i ∈ Finset.range N,
        if u i < t ∧ t ≤ u (i + 1) then
          e i * ((w (V i + δ - m i) - w (V i - m i)) / h) else 0) ∂μ) := by
  classical
  let H (i : ℕ) : ℝ≥0 × ℝ → ℝ := fun p =>
    if u i < p.1 ∧ p.1 ≤ u (i + 1) then -p.2 else 0
  let c (i : ℕ) := e i * ((w (V i - m i) - w (V i)) / m i)
  let z (i : ℕ) := e i * ((w (V i + δ - m i) - w (V i - m i)) / h)
  let F (i : ℕ) : ℝ≥0 × ℝ → ℝ := fun p => c i * H i p
  let G (i : ℕ) : ℝ≥0 → ℝ := (Ioc (u i) (u (i + 1))).indicator (fun _ => z i)
  have hFI (i : ℕ) (hi : i ∈ Finset.range N) : Integrable (F i) ν :=
    (hmass i hi).1.const_mul (c i)
  have hGI (i : ℕ) : Integrable (G i) μ :=
    (integrable_const (z i)).indicator measurableSet_Ioc
  have hFint (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ p, F i p ∂ν) = e i * (w (V i - m i) - w (V i)) := by
    dsimp [F]
    rw [integral_const_mul, (hmass i hi).2]
    dsimp [c]
    by_cases hm : m i = 0
    · simp [hm]
    · field_simp
  have hGint (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ t, G i t ∂μ) = e i * (w (V i + δ - m i) - w (V i - m i)) := by
    dsimp [G]
    rw [integral_indicator measurableSet_Ioc, setIntegral_const]
    change (μ (Ioc (u i) (u (i + 1)))).toReal • z i = _
    rw [hvol i hi, ENNReal.toReal_ofReal hh.le, smul_eq_mul]
    dsimp [z]
    field_simp
  have hFval (i : ℕ) (p : ℝ≥0 × ℝ) : F i p =
      if u i < p.1 ∧ p.1 ≤ u (i + 1) then
        e i * ((w (V i - m i) - w (V i)) / m i) * (-p.2) else 0 := by
    dsimp [F, H, c]
    split_ifs <;> simp only [mul_zero]
  have hGval (i : ℕ) (t : ℝ≥0) : G i t =
      if u i < t ∧ t ≤ u (i + 1) then
        e i * ((w (V i + δ - m i) - w (V i - m i)) / h) else 0 := by
    simp only [G, z, Set.indicator_apply, mem_Ioc]
  have hsumF : (∫ p, ∑ i ∈ Finset.range N, F i p ∂ν) =
      ∑ i ∈ Finset.range N, e i * (w (V i - m i) - w (V i)) := by
    rw [integral_finset_sum _ hFI]
    exact Finset.sum_congr rfl (fun i hi => hFint i hi)
  have hsumG : (∫ t, ∑ i ∈ Finset.range N, G i t ∂μ) =
      ∑ i ∈ Finset.range N, e i * (w (V i + δ - m i) - w (V i - m i)) := by
    rw [integral_finset_sum _ (fun i _ => hGI i)]
    exact Finset.sum_congr rfl (fun i hi => hGint i hi)
  simp_rw [hFval] at hsumF
  simp_rw [hGval] at hsumG
  rw [hsumF, hsumG, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end
