-- Prove2me | solution 1 for SamuelCahnProphet.Median.eq_1_4_indep
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:52.640509+00:00
-- url     : https://prove2.me/submissions/582f9be4-1a9d-4014-9be3-e90fb9e687e1

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

open scoped Classical in
lemma Z_indep_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (i : Fin n) (S : Set ℝ) (hS : MeasurableSet S) (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, (if (∀ j < i, X j ω ∈ S) then f (X i ω) else 0) ∂P =
      (∫⁻ ω, f (X i ω) ∂P) * P {ω | ∀ j < i, X j ω ∈ S} := by
  classical
  let Y : Ω → (Finset.Iio i → ℝ) := fun a j => X j a
  let Y' : Ω → (({i} : Finset (Fin n)) → ℝ) := fun a j => X j a
  have hdisj : Disjoint (Finset.Iio i) ({i} : Finset (Fin n)) := by
    simp
  have hind2 : IndepFun Y Y' P := hind.indepFun_finset (Finset.Iio i) {i} hdisj hXm
  let B : Set (Finset.Iio i → ℝ) := {y | ∀ j, y j ∈ S}
  have hB : MeasurableSet B := by
    have : B = ⋂ j, (fun y : (Finset.Iio i → ℝ) => y j) ⁻¹' S := by
      ext y; simp [B]
    rw [this]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) hS)
  let φ : (Finset.Iio i → ℝ) → ENNReal := B.indicator (fun _ => 1)
  let ψ : (({i} : Finset (Fin n)) → ℝ) → ENNReal := fun y => f (y ⟨i, Finset.mem_singleton_self i⟩)
  have hφ : Measurable φ := measurable_const.indicator hB
  have hψ : Measurable ψ := hf.comp (measurable_pi_apply _)
  have hind3 : IndepFun (φ ∘ Y) (ψ ∘ Y') P := hind2.comp hφ hψ
  have hYm : Measurable Y := measurable_pi_lambda _ (fun j => hXm j)
  have hY'm : Measurable Y' := measurable_pi_lambda _ (fun j => hXm j)
  have hA : {ω | ∀ j < i, X j ω ∈ S} = Y ⁻¹' B := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, B, Y]
    constructor
    · intro h j
      exact h j (Finset.mem_Iio.mp j.2)
    · intro h j hj
      exact h ⟨j, Finset.mem_Iio.mpr hj⟩
  have hAm : MeasurableSet {ω | ∀ j < i, X j ω ∈ S} := by
    rw [hA]; exact hYm hB
  have e1 : ∀ ω, (if (∀ j < i, X j ω ∈ S) then f (X i ω) else 0) =
      ((φ ∘ Y) * (ψ ∘ Y')) ω := by
    intro ω
    have : (∀ j < i, X j ω ∈ S) ↔ Y ω ∈ B := by
      have := Set.ext_iff.mp hA ω
      simpa using this
    by_cases h : (∀ j < i, X j ω ∈ S)
    · have hb : Y ω ∈ B := this.mp h
      have h1 : φ (Y ω) = 1 := by simp [φ, Set.indicator_of_mem hb]
      rw [if_pos h]
      show _ = φ (Y ω) * ψ (Y' ω)
      rw [h1, one_mul]
    · have hb : Y ω ∉ B := fun hh => h (this.mpr hh)
      have h1 : φ (Y ω) = 0 := by simp [φ, Set.indicator_of_notMem hb]
      rw [if_neg h]
      show _ = φ (Y ω) * ψ (Y' ω)
      rw [h1, zero_mul]
  simp_rw [e1]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hφ.comp hYm) (hψ.comp hY'm) hind3]
  have e2 : (∫⁻ ω, (φ ∘ Y) ω ∂P) = P {ω | ∀ j < i, X j ω ∈ S} := by
    rw [hA]
    have : (φ ∘ Y) = (Y ⁻¹' B).indicator (fun _ => (1 : ENNReal)) := by
      funext ω
      by_cases hb : Y ω ∈ B <;> simp [φ, hb]
    rw [this, lintegral_indicator_const (hYm hB)]
    simp
  have e3 : (∫⁻ ω, (ψ ∘ Y') ω ∂P) = ∫⁻ ω, f (X i ω) ∂P := by
    rfl
  rw [e2, e3, mul_comm]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (m : ℝ) :
    ∀ i : Fin n,
      (∫⁻ ω, (if i ≤ sRule X m ω then ENNReal.ofReal (X i ω - m) else 0) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) * P {ω | i ≤ sRule X m ω} := by
  intro i
  have h := Z_indep_split P X hXm hind i (Set.Iic m) measurableSet_Iic
    (fun x => ENNReal.ofReal (x - m)) (ENNReal.measurable_ofReal.comp (measurable_id.sub_const m))
  have e : ∀ ω, (i ≤ sRule X m ω ↔ ∀ j < i, X j ω ∈ Set.Iic m) := by
    intro ω; simp [Z_sRule_le_iff]
  simp_rw [e]
  exact h
