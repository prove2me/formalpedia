-- Prove2me | solution 1 for SamuelCahnProphet.Median.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:15:33.077257+00:00
-- url     : https://prove2.me/submissions/d38a0a97-edd3-4b2c-985c-3b113b28eea1

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

lemma Z_meas_max_lt {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (m : ℝ) : MeasurableSet {ω | maxX X ω < m} := by
  have : {ω | maxX X ω < m} = ⋂ i, {ω | X i ω < m} := by
    ext ω
    simp [maxX, Finset.sup'_lt_iff]
  rw [this]
  exact MeasurableSet.iInter (fun i => measurableSet_lt (hXm i) measurable_const)

lemma Z_e14f {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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

lemma Z_e14d {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (X (sRule X m ω) ω - m) ∂P) =
      ∑ i : Fin n, ∫⁻ ω, (if i ≤ sRule X m ω
        then ENNReal.ofReal (X i ω - m) else 0) ∂P := by
  have key : ∀ ω, ENNReal.ofReal (X (sRule X m ω) ω - m) =
      ∑ i : Fin n, (if i ≤ sRule X m ω then ENNReal.ofReal (X i ω - m) else 0) := by
    intro ω
    rw [Finset.sum_eq_single (sRule X m ω)]
    · simp
    · intro i _ hne
      by_cases h : i ≤ sRule X m ω
      · have hlt : i < sRule X m ω := lt_of_le_of_ne h hne
        have := (Z_sRule_le_iff X m ω _).mp le_rfl i hlt
        rw [if_pos h, ENNReal.ofReal_of_nonpos (by linarith)]
      · rw [if_neg h]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [key]
  rw [lintegral_finset_sum]
  intro i _
  exact Measurable.ite (Z_meas_sRule X hXm m i)
    (ENNReal.measurable_ofReal.comp ((hXm i).sub_const m)) measurable_const

lemma Z_e14i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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

lemma Z_etd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (m : ℝ) (hm : 0 ≤ m) :
    EplusT P X m = ENNReal.ofReal m * (1 - P {ω | maxX X ω < m}) +
      ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) *
        P {ω | i ≤ tRule X m ω} := by
  have hA : MeasurableSet {ω | m ≤ maxX X ω} := by
    have : {ω | m ≤ maxX X ω} = {ω | maxX X ω < m}ᶜ := by
      ext ω; simp
    rw [this]; exact (Z_meas_max_lt X hXm m).compl
  have hPA : P {ω | m ≤ maxX X ω} = 1 - P {ω | maxX X ω < m} := by
    have : {ω | m ≤ maxX X ω} = {ω | maxX X ω < m}ᶜ := by
      ext ω; simp
    rw [this, prob_compl_eq_one_sub (Z_meas_max_lt X hXm m)]
  have key : ∀ ω, (if m ≤ X (tRule X m ω) ω then ENNReal.ofReal (X (tRule X m ω) ω) else 0)
      = {ω | m ≤ maxX X ω}.indicator (fun _ => ENNReal.ofReal m) ω
        + ENNReal.ofReal (X (tRule X m ω) ω - m) := by
    intro ω
    by_cases h : m ≤ maxX X ω
    · have h' : m ≤ X (tRule X m ω) ω := (Z_t_le_iff X m ω).mpr h
      rw [if_pos h', Set.indicator_of_mem (by exact h), ← ENNReal.ofReal_add hm (by linarith)]
      congr 1; ring
    · have h' : ¬ m ≤ X (tRule X m ω) ω := fun h2 => h ((Z_t_le_iff X m ω).mp h2)
      rw [if_neg h', Set.indicator_of_notMem (by exact h)]
      rw [ENNReal.ofReal_of_nonpos (by linarith [not_le.mp h'])]
      simp
  have key2 : ∀ ω, ENNReal.ofReal (X (tRule X m ω) ω - m) =
      ∑ i : Fin n, (if i ≤ tRule X m ω then ENNReal.ofReal (X i ω - m) else 0) := by
    intro ω
    rw [Finset.sum_eq_single (tRule X m ω)]
    · simp
    · intro i _ hne
      by_cases h : i ≤ tRule X m ω
      · have hlt : i < tRule X m ω := lt_of_le_of_ne h hne
        have := (Z_tRule_le_iff X m ω _).mp le_rfl i hlt
        rw [if_pos h, ENNReal.ofReal_of_nonpos (by linarith)]
      · rw [if_neg h]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold EplusT
  simp_rw [key]
  rw [lintegral_add_left (measurable_const.indicator hA), lintegral_indicator_const hA, hPA]
  congr 1
  simp_rw [key2]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := Z_indep_split P X hXm hind i (Set.Iio m) measurableSet_Iio
      (fun x => ENNReal.ofReal (x - m)) (ENNReal.measurable_ofReal.comp (measurable_id.sub_const m))
    have e : ∀ ω, (i ≤ tRule X m ω ↔ ∀ j < i, X j ω ∈ Set.Iio m) := by
      intro ω; simp [Z_tRule_le_iff]
    simp_rw [e]
    exact h
  · intro i _
    exact Measurable.ite (Z_meas_tRule X hXm m i)
      (ENNReal.measurable_ofReal.comp ((hXm i).sub_const m)) measurable_const

lemma Z_e13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (m : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤
        ENNReal.ofReal m + ∫⁻ ω, ENNReal.ofReal (maxX X ω - m) ∂P ∧
    ENNReal.ofReal m + (∫⁻ ω, ENNReal.ofReal (maxX X ω - m) ∂P) ≤
        ENNReal.ofReal m + SamuelCahnProphet.Median.beta P X m := by
  have hmax : Measurable (maxX X) := by
    have : ∀ ω, maxX X ω = Finset.univ.sup' Finset.univ_nonempty (fun i => X i) ω := by
      intro ω; simp [maxX]
    have h2 : Measurable (Finset.univ.sup' Finset.univ_nonempty (fun i => X i)) :=
      Finset.measurable_sup' _ (fun i _ => hXm i)
    have : maxX X = Finset.univ.sup' Finset.univ_nonempty (fun i => X i) := funext this
    rw [this]; exact h2
  constructor
  · calc (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P)
        ≤ ∫⁻ ω, (ENNReal.ofReal m + ENNReal.ofReal (maxX X ω - m)) ∂P := by
          apply lintegral_mono
          intro ω
          have := ENNReal.ofReal_add_le (p := m) (q := maxX X ω - m)
          simpa using this
      _ = ENNReal.ofReal m + ∫⁻ ω, ENNReal.ofReal (maxX X ω - m) ∂P := by
          rw [lintegral_add_left measurable_const]
          simp
  · gcongr
    unfold SamuelCahnProphet.Median.beta
    rw [← lintegral_finset_sum]
    · apply lintegral_mono
      intro ω
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n)) (fun i => X i ω)
      have : maxX X ω = X k ω := hk
      show ENNReal.ofReal (maxX X ω - m) ≤ ∑ b, ENNReal.ofReal (X b ω - m)
      rw [this]
      exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (X i ω - m)) (fun _ _ => zero_le)
        (Finset.mem_univ k)
    · intro i _
      exact ENNReal.measurable_ofReal.comp ((hXm i).sub_const m)


lemma Z_psge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    ∀ i : Fin n, 1 - P {ω | m < maxX X ω} ≤ P {ω | i ≤ sRule X m ω} := by
  intro i
  rw [← prob_compl_eq_one_sub (Z_meas_lt_max X hXm m)]
  apply measure_mono
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω
  simp only [Set.mem_ofPred_eq, Z_sRule_le_iff]
  intro j _
  exact (Z_le_max X ω j).trans hω


lemma Z_ptge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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


lemma Z_half (p : ENNReal) (h : p ≤ 1 / 2) : p + (1 - p) = 1 ∧ p ≤ 1 - p ∧ 1 - p ≠ 0 := by
  have h1 : p ≤ 1 := h.trans (by
    have := ENNReal.add_halves (1 : ENNReal)
    calc (1 : ENNReal) / 2 ≤ 1 / 2 + 1 / 2 := le_self_add
      _ = 1 := this)
  refine ⟨add_tsub_cancel_of_le h1, ?_, ?_⟩
  · apply ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top h1)
    calc p + p ≤ 1 / 2 + 1 / 2 := add_le_add h h
      _ = 1 := ENNReal.add_halves 1
  · have : p < 1 := lt_of_le_of_lt h (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top)
    exact (tsub_pos_iff_lt.mpr this).ne'

lemma Z_key (x y u v : ENNReal) (hxy : x ≤ y) (huv : u ≤ v) (h1 : u + v = 1) (hv : v ≠ 0) :
    x + y ≤ 2 * (x * u + y * v) := by
  by_cases hy : y = ⊤
  · rw [hy, ENNReal.top_mul hv]
    simp
  · have hx : x ≠ ⊤ := ne_top_of_le_ne_top hy hxy
    have hv1 : v ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    have hu1 : u ≠ ⊤ := ne_top_of_le_ne_top hv1 huv
    lift x to NNReal using hx
    lift y to NNReal using hy
    lift u to NNReal using hu1
    lift v to NNReal using hv1
    have h1' : u + v = 1 := by exact_mod_cast h1
    have : (x : ENNReal) + y ≤ 2 * (x * u + y * v) := by
      have key : x + y ≤ 2 * (x * u + y * v) := by
        rw [← NNReal.coe_le_coe]
        push_cast
        have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
        have huv' : (u : ℝ) ≤ v := by exact_mod_cast huv
        have h1'' : (u : ℝ) + v = 1 := by exact_mod_cast h1'
        nlinarith [mul_nonneg (sub_nonneg.mpr hxy') (sub_nonneg.mpr huv')]
      exact_mod_cast key
    exact this

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hind : iIndepFun X P) (m : ℝ)
    (hmed : IsMedian P (maxX X) m) :
    (ENNReal.ofReal m ≤ SamuelCahnProphet.Median.beta P X m →
      (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤ 2 * EplusS P X m ∧
      2 * EplusS P X m ≤ 2 * expStop P X (sRule X m)) ∧
    (SamuelCahnProphet.Median.beta P X m ≤ ENNReal.ofReal m →
      (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤ 2 * EplusT P X m ∧
      2 * EplusT P X m ≤ 2 * expStop P X (tRule X m)) := by
  obtain ⟨hmed1, hmed2⟩ := hmed
  have hm0 : 0 ≤ m := by
    by_contra hneg
    push Not at hneg
    have hA := Z_meas_lt_max X hXm m
    have hae : ∀ᵐ ω ∂P, ω ∈ {ω | m < maxX X ω} := by
      filter_upwards [hXnn 0] with ω hω
      exact lt_of_lt_of_le hneg (hω.trans (Z_le_max X ω 0))
    have h0 : P {ω | m < maxX X ω}ᶜ = 0 := ae_iff.mp hae
    have h1 : P {ω | m < maxX X ω} = 1 := (prob_compl_eq_zero_iff hA).mp h0
    rw [h1] at hmed2
    exact absurd hmed2 (not_le.mpr (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top))
  have hE : (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤ ENNReal.ofReal m + SamuelCahnProphet.Median.beta P X m := by
    have := Z_e13 P X hXm m
    exact this.1.trans this.2
  have hS : EplusS P X m = ENNReal.ofReal m * P {ω | m < maxX X ω} +
      ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) * P {ω | i ≤ sRule X m ω} := by
    rw [Z_e14f P X hXm m hm0, Z_e14d P X hXm m]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => Z_e14i P X hXm hind m i)
  have hT := Z_etd P X hXm hind m hm0
  constructor
  · intro hmb
    refine ⟨?_, ?_⟩
    · obtain ⟨hq1, hq2, hq3⟩ := Z_half _ hmed2
      have hsum : SamuelCahnProphet.Median.beta P X m * (1 - P {ω | m < maxX X ω}) ≤
          ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) * P {ω | i ≤ sRule X m ω} := by
        unfold SamuelCahnProphet.Median.beta
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun i _ => mul_le_mul' (le_refl _) (Z_psge P X hXm m i))
      calc (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P)
          ≤ ENNReal.ofReal m + SamuelCahnProphet.Median.beta P X m := hE
        _ ≤ 2 * (ENNReal.ofReal m * P {ω | m < maxX X ω}
            + SamuelCahnProphet.Median.beta P X m * (1 - P {ω | m < maxX X ω})) :=
            Z_key _ _ _ _ hmb hq2 hq1 hq3
        _ ≤ 2 * EplusS P X m := by
            rw [hS]; gcongr
    · gcongr
      unfold EplusS expStop
      apply lintegral_mono
      intro ω
      dsimp only
      split_ifs <;> simp
  · intro hbm
    refine ⟨?_, ?_⟩
    · obtain ⟨hq1, hq2, hq3⟩ := Z_half _ hmed1
      have hsum : SamuelCahnProphet.Median.beta P X m * P {ω | maxX X ω < m} ≤
          ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) * P {ω | i ≤ tRule X m ω} := by
        unfold SamuelCahnProphet.Median.beta
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun i _ => mul_le_mul' (le_refl _) (Z_ptge P X hXm m i))
      calc (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P)
          ≤ ENNReal.ofReal m + SamuelCahnProphet.Median.beta P X m := hE
        _ = SamuelCahnProphet.Median.beta P X m + ENNReal.ofReal m := add_comm _ _
        _ ≤ 2 * (SamuelCahnProphet.Median.beta P X m * P {ω | maxX X ω < m}
            + ENNReal.ofReal m * (1 - P {ω | maxX X ω < m})) :=
            Z_key _ _ _ _ hbm hq2 hq1 hq3
        _ = 2 * (ENNReal.ofReal m * (1 - P {ω | maxX X ω < m}) +
            SamuelCahnProphet.Median.beta P X m * P {ω | maxX X ω < m}) := by
            rw [add_comm (SamuelCahnProphet.Median.beta P X m * _)]
        _ ≤ 2 * EplusT P X m := by
            rw [hT]; gcongr
    · gcongr
      unfold EplusT expStop
      apply lintegral_mono
      intro ω
      dsimp only
      split_ifs <;> simp
