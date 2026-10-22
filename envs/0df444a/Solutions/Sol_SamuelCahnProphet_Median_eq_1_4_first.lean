-- Prove2me | solution 1 for SamuelCahnProphet.Median.eq_1_4_first
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:01.690989+00:00
-- url     : https://prove2.me/submissions/418d82da-e902-4381-be1a-d8427793a474

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

lemma Z_s_lt_iff {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) :
    c < X (sRule X c ω) ω ↔ c < maxX X ω := by
  constructor
  · intro h
    exact h.trans_le (Z_le_max X ω _)
  · intro h
    obtain ⟨k, hk⟩ := (Z_lt_max_iff X c ω).mp h
    by_contra hcon
    have hs : sRule X c ω = ⊤ := by
      rcases Z_sRule_mem X c ω with h1 | h1
      · exact absurd h1 hcon
      · exact h1
    have hle : ∀ j < sRule X c ω, X j ω ≤ c := (Z_sRule_le_iff X c ω _).mp le_rfl
    rcases lt_or_eq_of_le (le_top : k ≤ ⊤) with hlt | heq
    · rw [← hs] at hlt
      linarith [hle k hlt]
    · rw [heq, ← hs] at hk
      exact hcon hk

lemma Z_t_le_iff {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) :
    c ≤ X (tRule X c ω) ω ↔ c ≤ maxX X ω := by
  constructor
  · intro h
    exact h.trans (Z_le_max X ω _)
  · intro h
    have : ∃ k, c ≤ X k ω := by
      unfold maxX at h
      rw [Finset.le_sup'_iff] at h
      simpa using h
    obtain ⟨k, hk⟩ := this
    by_contra hcon
    have hs : tRule X c ω = ⊤ := by
      rcases Z_tRule_mem X c ω with h1 | h1
      · exact absurd h1 hcon
      · exact h1
    have hle : ∀ j < tRule X c ω, X j ω < c := (Z_tRule_le_iff X c ω _).mp le_rfl
    rcases lt_or_eq_of_le (le_top : k ≤ ⊤) with hlt | heq
    · rw [← hs] at hlt
      linarith [hle k hlt]
    · rw [heq, ← hs] at hk
      exact hcon hk

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) (hm : 0 ≤ m) :
    EplusS P X m = ENNReal.ofReal m * P {ω | m < maxX X ω} +
      ∫⁻ ω, ENNReal.ofReal (X (sRule X m ω) ω - m) ∂P := by
  have hA := Z_meas_lt_max X hXm m
  have key : ∀ ω, (if m < X (sRule X m ω) ω then ENNReal.ofReal (X (sRule X m ω) ω) else 0)
      = {ω | m < maxX X ω}.indicator (fun _ => ENNReal.ofReal m) ω
        + ENNReal.ofReal (X (sRule X m ω) ω - m) := by
    intro ω
    by_cases h : m < maxX X ω
    · have h' : m < X (sRule X m ω) ω := (Z_s_lt_iff X m ω).mpr h
      rw [if_pos h', Set.indicator_of_mem (by exact h), ← ENNReal.ofReal_add hm (by linarith)]
      congr 1; ring
    · have h' : ¬ m < X (sRule X m ω) ω := fun h2 => h ((Z_s_lt_iff X m ω).mp h2)
      rw [if_neg h', Set.indicator_of_notMem (by exact h)]
      rw [ENNReal.ofReal_of_nonpos (by linarith [not_lt.mp h'])]
      simp
  unfold EplusS
  simp_rw [key]
  rw [lintegral_add_left (measurable_const.indicator hA), lintegral_indicator_const hA]
