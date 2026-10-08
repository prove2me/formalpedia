-- Prove2me | solution 1 for RegretBandits.Stochastic.pseudo_regret_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:35:22.680112+00:00
-- url     : https://prove2.me/submissions/3fb8087b-749d-4640-b8f5-642b65b2ee0c

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model

set_option autoImplicit false

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem pullCount_cast_eq_7d8a {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (n : ℕ)
    (ω : Ω) :
    (pullCount I i n ω : ℝ) = ∑ t ∈ Finset.range n, if I (t + 1) ω = i then (1 : ℝ) else 0 := by
  rw [pullCount, Finset.card_filter]
  push_cast
  rfl

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem pullCount_integrable_7d8a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (i : Fin K) (n : ℕ) :
    Integrable (fun ω => (pullCount I i n ω : ℝ)) P := by
  simp_rw [pullCount_cast_eq_7d8a]
  refine integrable_finsetSum _ (fun t _ => ?_)
  have hm : MeasurableSet {ω | I (t + 1) ω = i} := (hI (t + 1)) (measurableSet_singleton i)
  have : (fun ω => if I (t + 1) ω = i then (1 : ℝ) else 0)
      = Set.indicator {ω | I (t + 1) ω = i} (fun _ => (1 : ℝ)) := by
    funext ω; simp [Set.indicator]
  rw [this]
  exact (integrable_const (1 : ℝ)).indicator hm

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem sum_pullCount_7d8a {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (n : ℕ) (ω : Ω) :
    ∑ i, (pullCount I i n ω : ℝ) = n := by
  simp_rw [pullCount_cast_eq_7d8a]
  rw [Finset.sum_comm]
  simp

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem sum_pullCount_mul_7d8a {Ω : Type*} {K : ℕ} (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K) (n : ℕ)
    (ω : Ω) :
    ∑ i, (pullCount I i n ω : ℝ) * μ i = ∑ t ∈ Finset.range n, μ (I (t + 1) ω) := by
  simp_rw [pullCount_cast_eq_7d8a, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (n : ℕ) :
    pseudoRegretBar P μ I n =
        (∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P) * bestMean μ
          - ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P ∧
      pseudoRegretBar P μ I n = ∑ i, gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by
  have hint := pullCount_integrable_7d8a P I hI
  have hsum : ∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P = n := by
    rw [← integral_finsetSum _ (fun i _ => hint i n)]
    simp_rw [sum_pullCount_7d8a]
    simp
  have hmul : ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P
      = ∑ i, (∫ ω, (pullCount I i n ω : ℝ) ∂P) * μ i := by
    rw [integral_finsetSum _ (fun i _ => (hint i n).mul_const (μ i))]
    simp_rw [integral_mul_const]
  have h1 : pseudoRegretBar P μ I n =
      (∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P) * bestMean μ
        - ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P := by
    unfold pseudoRegretBar
    rw [hsum]
    simp_rw [sum_pullCount_mul_7d8a]
  refine ⟨h1, ?_⟩
  rw [h1, hmul, hsum]
  rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold gap
  ring
