-- Prove2me | solution 1 for SamuelCahnProphet.Median.prob_tRule_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:05:50.284716+00:00
-- url     : https://prove2.me/submissions/fd4eeac7-e77d-4fef-b509-65299b8969ce

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory SamuelCahnProphet.Median

lemma Z_sRule_mem {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) :
    c < X (sRule X c ω) ω ∨ sRule X c ω = ⊤ := by
  classical
  unfold sRule
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun i : Fin n => c < X i ω ∨ i = ⊤)) ⟨⊤, by simp⟩)).2

lemma Z_sRule_min {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω)
    (k : Fin n) (hk : c < X k ω ∨ k = ⊤) : sRule X c ω ≤ k := by
  classical
  unfold sRule
  exact Finset.min'_le (Finset.univ.filter (fun i : Fin n => c < X i ω ∨ i = ⊤)) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

lemma Z_tRule_mem {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) :
    c ≤ X (tRule X c ω) ω ∨ tRule X c ω = ⊤ := by
  classical
  unfold tRule
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun i : Fin n => c ≤ X i ω ∨ i = ⊤)) ⟨⊤, by simp⟩)).2

lemma Z_tRule_min {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω)
    (k : Fin n) (hk : c ≤ X k ω ∨ k = ⊤) : tRule X c ω ≤ k := by
  classical
  unfold tRule
  exact Finset.min'_le (Finset.univ.filter (fun i : Fin n => c ≤ X i ω ∨ i = ⊤)) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)

lemma Z_sRule_le_iff {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω)
    (i : Fin n) : i ≤ sRule X c ω ↔ ∀ j < i, X j ω ≤ c := by
  constructor
  · intro h j hj
    by_contra hc
    push Not at hc
    exact absurd hj (not_lt.mpr (h.trans (Z_sRule_min X c ω j (Or.inl hc))))
  · intro h
    rcases Z_sRule_mem X c ω with hk | hk
    · by_contra hlt
      push Not at hlt
      have := h _ hlt
      linarith
    · rw [hk]; exact le_top

lemma Z_tRule_le_iff {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω)
    (i : Fin n) : i ≤ tRule X c ω ↔ ∀ j < i, X j ω < c := by
  constructor
  · intro h j hj
    by_contra hc
    push Not at hc
    exact absurd hj (not_lt.mpr (h.trans (Z_tRule_min X c ω j (Or.inl hc))))
  · intro h
    rcases Z_tRule_mem X c ω with hk | hk
    · by_contra hlt
      push Not at hlt
      have := h _ hlt
      linarith
    · rw [hk]; exact le_top

lemma Z_lt_max_iff {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (m : ℝ) (ω : Ω) :
    m < maxX X ω ↔ ∃ i, m < X i ω := by
  unfold maxX
  rw [Finset.lt_sup'_iff]
  simp

lemma Z_le_max {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (ω : Ω) (i : Fin n) :
    X i ω ≤ maxX X ω := by
  unfold maxX
  exact Finset.le_sup' (fun i => X i ω) (Finset.mem_univ i)

lemma Z_meas_lt_max {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (m : ℝ) : MeasurableSet {ω | m < maxX X ω} := by
  have : {ω | m < maxX X ω} = ⋃ i, {ω | m < X i ω} := by
    ext ω; simp [Z_lt_max_iff]
  rw [this]
  exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const (hXm i))

lemma Z_meas_sRule {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (m : ℝ) (i : Fin n) :
    MeasurableSet {ω | i ≤ sRule X m ω} := by
  have : {ω | i ≤ sRule X m ω} = ⋂ j, {ω | j < i → X j ω ≤ m} := by
    ext ω; simp [Z_sRule_le_iff]
  rw [this]
  refine MeasurableSet.iInter (fun j => ?_)
  by_cases h : j < i
  · simp only [h, forall_true_left]
    exact measurableSet_le (hXm j) measurable_const
  · simp [h]

lemma Z_meas_tRule {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (m : ℝ) (i : Fin n) :
    MeasurableSet {ω | i ≤ tRule X m ω} := by
  have : {ω | i ≤ tRule X m ω} = ⋂ j, {ω | j < i → X j ω < m} := by
    ext ω; simp [Z_tRule_le_iff]
  rw [this]
  refine MeasurableSet.iInter (fun j => ?_)
  by_cases h : j < i
  · simp only [h, forall_true_left]
    exact measurableSet_lt (hXm j) measurable_const
  · simp [h]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    ∀ i : Fin n, P {ω | maxX X ω < m} ≤ P {ω | i ≤ tRule X m ω} := by
  intro i
  apply measure_mono
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_ofPred_eq, Z_tRule_le_iff]
  intro j _
  exact (Z_le_max X ω j).trans_lt hω
