-- Prove2me | solution 1 for PriceSwitch.Markdown.theorem1_markdown_threshold
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T15:25:21.52664+00:00
-- url     : https://prove2.me/submissions/2c7e86da-fcff-4177-a315-87d5c6bb645e

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations PriceSwitch.Markdown

namespace DP872

local instance instExp1 : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure one_pos

section General

variable {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)

lemma measurableSet_mem_arr (hT : ∀ i, Measurable (T i)) (u : ℝ) (n : ℕ) :
    MeasurableSet {ω | 1 ≤ n ∧ arrivalTime T n ω ≤ u} := by
  have hm : Measurable fun ω => arrivalTime T n ω := by
    unfold arrivalTime
    exact Finset.measurable_sum _ fun i _ => hT i
  exact (MeasurableSet.const (1 ≤ n)).inter (measurableSet_le hm measurable_const)

lemma measurable_countingProcess (hT : ∀ i, Measurable (T i)) (u : ℝ) :
    Measurable (countingProcess T u) := by
  refine measurable_to_countable' fun k => ?_
  have hmem := measurableSet_mem_arr T hT u
  have hinf : MeasurableSet {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} := by
    have : {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} =
        ⋂ M : ℕ, ⋃ n : ℕ, {ω : Ω | M ≤ n} ∩ {ω | 1 ≤ n ∧ arrivalTime T n ω ≤ u} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h M
        obtain ⟨n, hn, hMn⟩ := h.exists_gt M
        exact ⟨n, hMn.le, hn⟩
      · intro h
        refine Set.infinite_of_not_bddAbove ?_
        rintro ⟨B, hB⟩
        obtain ⟨n, hBn, hn⟩ := h (B + 1)
        have := hB hn
        omega
    rw [this]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
      (MeasurableSet.const _).inter (hmem n)
  have hfin : ∀ F : Finset ℕ,
      MeasurableSet {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = ↑F} := by
    intro F
    have : {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = ↑F} =
        ⋂ n : ℕ, {ω | (1 ≤ n ∧ arrivalTime T n ω ≤ u) ↔ n ∈ F} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.ext_iff, Finset.mem_coe]
    rw [this]
    refine MeasurableSet.iInter fun n => ?_
    by_cases h : n ∈ F
    · simp only [h, iff_true]
      exact hmem n
    · simp only [h, iff_false]
      exact (hmem n).compl
  have : countingProcess T u ⁻¹' {k} =
      (⋃ (F : Finset ℕ) (_ : F.card = k),
        {ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u} = (F : Set ℕ)}) ∪
        ({ω | {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Infinite} ∩ {_ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, countingProcess, Set.mem_union,
      Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases hf : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ u}.Finite
      · left
        refine ⟨hf.toFinset, ?_, hf.coe_toFinset.symm⟩
        rw [← h, Set.ncard_eq_toFinset_card _ hf]
      · right
        exact ⟨hf, by rw [← h, Set.Infinite.ncard hf]⟩
    · rintro (⟨F, hF, hA⟩ | ⟨hinf, rfl⟩)
      · rw [hA, Set.ncard_coe_finset, hF]
      · exact Set.Infinite.ncard hinf
  rw [this]
  exact (MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => hfin F).union (hinf.inter (MeasurableSet.const _))

lemma history_le (hT : ∀ i, Measurable (T i)) (s : ℝ) :
    history T s ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun u _ => (measurable_countingProcess T hT u).comap_le

/-- Sets determined by the counting process at countably many times in `[0, s]`. -/
def detSpace (s : ℝ) : MeasurableSpace Ω where
  MeasurableSet' E := ∃ D : Set ℝ, D.Countable ∧ D ⊆ Set.Icc 0 s ∧
    ∀ ω ω', (∀ u ∈ D, countingProcess T u ω = countingProcess T u ω') → (ω ∈ E ↔ ω' ∈ E)
  measurableSet_empty := ⟨∅, Set.countable_empty, Set.empty_subset _, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl E := by
    rintro ⟨D, hD, hDs, h⟩
    exact ⟨D, hD, hDs, fun ω ω' hw => not_congr (h ω ω' hw)⟩
  measurableSet_iUnion f hf := by
    choose D hD hDs h using hf
    refine ⟨⋃ i, D i, Set.countable_iUnion hD, Set.iUnion_subset hDs, fun ω ω' hw => ?_⟩
    simp only [Set.mem_iUnion]
    exact exists_congr fun i => h i ω ω' fun u hu => hw u (Set.mem_iUnion.2 ⟨i, hu⟩)

lemma history_det (s : ℝ) {E : Set Ω} (hE : MeasurableSet[history T s] E) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ Set.Icc 0 s ∧
      ∀ ω ω', (∀ u ∈ D, countingProcess T u ω = countingProcess T u ω') → (ω ∈ E ↔ ω' ∈ E) := by
  have hle : history T s ≤ detSpace T s := by
    refine iSup₂_le fun u hu => ?_
    intro E hE
    obtain ⟨C, -, rfl⟩ := hE
    exact ⟨{u}, Set.countable_singleton u, Set.singleton_subset_iff.2 hu,
      fun ω ω' h => by simp only [Set.mem_preimage, h u rfl]⟩
  exact hle E hE

end General

/-! ## The canonical model -/

abbrev Ω0 := ℕ → ℝ

def T0 : ℕ → Ω0 → ℝ := fun i ω => ω i

lemma T0_meas (i : ℕ) : Measurable (T0 i) := measurable_pi_apply i

lemma arr_succ (ω : Ω0) (n : ℕ) : arrivalTime T0 (n + 1) ω = arrivalTime T0 n ω + ω n := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_one (ω : Ω0) : arrivalTime T0 1 ω = ω 0 := by simp [arrivalTime, T0]

lemma arr_two (ω : Ω0) : arrivalTime T0 2 ω = ω 0 + ω 1 := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_three (ω : Ω0) : arrivalTime T0 3 ω = ω 0 + ω 1 + ω 2 := by
  simp [arrivalTime, T0, Finset.sum_range_succ]

lemma arr_mono {ω : Ω0} (hω : ∀ i, 0 < ω i) : StrictMono fun n => arrivalTime T0 n ω :=
  strictMono_nat_of_lt_succ fun n => by rw [arr_succ]; linarith [hω n]

lemma cnt_zero {ω : Ω0} {u : ℝ} (h : ∀ n, 1 ≤ n → u < arrivalTime T0 n ω) :
    countingProcess T0 u ω = 0 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    exact h n
  simp [countingProcess, this]

lemma cnt_one {ω : Ω0} {u : ℝ} (h1 : arrivalTime T0 1 ω ≤ u)
    (h : ∀ n, 2 ≤ n → u < arrivalTime T0 n ω) : countingProcess T0 u ω = 1 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = {1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn1, hn⟩
      by_contra hne
      have := h n (by omega)
      linarith
    · rintro rfl
      exact ⟨le_rfl, h1⟩
  simp [countingProcess, this]

lemma cnt_two {ω : Ω0} {u : ℝ} (h1 : arrivalTime T0 1 ω ≤ u) (h2 : arrivalTime T0 2 ω ≤ u)
    (h : ∀ n, 3 ≤ n → u < arrivalTime T0 n ω) : countingProcess T0 u ω = 2 := by
  have : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} = {1, 2} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn1, hn⟩
      by_contra hne
      push_neg at hne
      have := h n (by omega)
      linarith
    · rintro (rfl | rfl)
      · exact ⟨le_rfl, h1⟩
      · exact ⟨by norm_num, h2⟩
  rw [countingProcess, this, Set.ncard_pair (by norm_num)]

lemma cnt_ne_one {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (h2 : arrivalTime T0 2 ω ≤ u) :
    countingProcess T0 u ω ≠ 1 := by
  have h1 : arrivalTime T0 1 ω ≤ u :=
    le_trans ((arr_mono hω).monotone (by norm_num : 1 ≤ 2)) h2
  show {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u}.ncard ≠ 1
  by_cases hf : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u}.Finite
  · have hsub : ({1, 2} : Set ℕ) ⊆ {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n ω ≤ u} := by
      intro n hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl
      · exact ⟨le_rfl, h1⟩
      · exact ⟨by norm_num, h2⟩
    have := Set.ncard_le_ncard hsub hf
    rw [Set.ncard_pair (by norm_num)] at this
    omega
  · rw [Set.Infinite.ncard hf]
    norm_num

lemma cnt_lt2 {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (hu : u < arrivalTime T0 2 ω) :
    countingProcess T0 u ω = if ω 0 ≤ u then 1 else 0 := by
  have hge : ∀ n, 2 ≤ n → u < arrivalTime T0 n ω := fun n hn =>
    lt_of_lt_of_le hu ((arr_mono hω).monotone hn)
  split_ifs with h
  · exact cnt_one (by rw [arr_one]; exact h) hge
  · refine cnt_zero fun n hn => ?_
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [arr_one]
      exact not_le.1 h
    · exact hge n hn2

lemma cnt_good {ω : Ω0} (hω : ∀ i, 0 < ω i) {u : ℝ} (hu : u < ω 0 + ω 1) :
    countingProcess T0 u ω = if ω 0 ≤ u then 1 else 0 :=
  cnt_lt2 hω (by rw [arr_two]; exact hu)

/-- A good path with first arrival at `s` and no second arrival before `s + 2`. -/
noncomputable def ws (s : ℝ) : Ω0 := fun i => if i = 0 then s else 2

lemma ws_pos {s : ℝ} (hs : 0 < s) : ∀ i, 0 < ws s i := fun i => by
  unfold ws
  split_ifs <;> linarith

lemma cnt_ws {s u : ℝ} (hs : 0 < s) (hu : u < s + 2) :
    countingProcess T0 u (ws s) = if s ≤ u then 1 else 0 := by
  have h := cnt_lt2 (ws_pos hs) (u := u) (by rw [arr_two]; simp [ws]; linarith)
  simpa [ws] using h

lemma measurable_ws : Measurable ws := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i = 0
  · simp only [ws, hi, if_true]
    exact measurable_id
  · simp only [ws, hi, if_false]
    exact measurable_const

/-- A bad path: one arrival at `s`, then arrivals decreasing to `s` from above, so the counting
process is `1` at `s` and `0` everywhere else. -/
noncomputable def sp (s : ℝ) : Ω0 := fun i =>
  if i = 0 then s else if i = 1 then 1 else 1 / (i : ℝ) - 1 / ((i : ℝ) - 1)

lemma sp_arr (s : ℝ) (j : ℕ) : arrivalTime T0 (j + 2) (sp s) = s + 1 / ((j : ℝ) + 1) := by
  induction j with
  | zero => simp [arrivalTime, T0, sp, Finset.sum_range_succ]
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by ring, arr_succ, ih]
    simp only [sp, show j + 2 ≠ 0 by omega, show j + 2 ≠ 1 by omega, if_false]
    push_cast
    have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (j : ℝ) + 2 - 1 = (j : ℝ) + 1 := by ring
    rw [h3]
    field_simp
    ring

lemma cnt_sp {s u : ℝ} : countingProcess T0 u (sp s) = if u = s then 1 else 0 := by
  have h1 : arrivalTime T0 1 (sp s) = s := by rw [arr_one]; simp [sp]
  have hgt : ∀ n, 2 ≤ n → s < arrivalTime T0 n (sp s) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    rw [sp_arr]
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  rcases lt_trichotomy u s with h | h | h
  · rw [if_neg h.ne]
    refine cnt_zero fun n hn => ?_
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [h1]
      exact h
    · exact h.trans (hgt n hn2)
  · subst h
    rw [if_pos rfl]
    exact cnt_one h1.le hgt
  · rw [if_neg h.ne']
    have hinf : {n : ℕ | 1 ≤ n ∧ arrivalTime T0 n (sp s) ≤ u}.Infinite := by
      obtain ⟨J, hJ⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      refine Set.infinite_of_forall_exists_gt fun M => ⟨M + J + 2, ⟨by omega, ?_⟩, by omega⟩
      rw [sp_arr]
      have : 1 / (((M + J : ℕ) : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      linarith
    exact Set.Infinite.ncard hinf


/-! ## The measure -/

section Measure

noncomputable def P0 : Measure Ω0 := Measure.infinitePi fun _ : ℕ => expMeasure (1 : ℝ)

lemma P0_prob : IsProbabilityMeasure P0 := by
  unfold P0
  infer_instance

lemma hT0 : IsExpInterarrivals P0 1 T0 where
  measurable := T0_meas
  indep := iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure (1 : ℝ))
    (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  law i := Measure.infinitePi_map_eval _ i

lemma mu_Iic_zero : expMeasure (1 : ℝ) (Set.Iic 0) = 0 := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, if_pos le_rfl]
  simp

lemma mu_Iic (c : ℝ) (hc : 0 ≤ c) :
    expMeasure (1 : ℝ) (Set.Iic c) = ENNReal.ofReal (1 - Real.exp (-c)) := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, if_pos hc, one_mul]

lemma mu_Ioc {c : ℝ} (hc : 0 < c) : expMeasure (1 : ℝ) (Set.Ioc 0 c) ≠ 0 := by
  intro h
  have hsub : Set.Iic c ⊆ Set.Ioc 0 c ∪ Set.Iic 0 := by
    intro x hx
    rcases le_or_gt x 0 with h' | h'
    · exact Or.inr h'
    · exact Or.inl ⟨h', hx⟩
  have := measure_mono_null hsub (measure_union_null h mu_Iic_zero)
  rw [mu_Iic c hc.le, ENNReal.ofReal_eq_zero] at this
  have : Real.exp (-c) < 1 := by
    have h := Real.exp_lt_exp.2 (show -c < 0 by linarith)
    rwa [Real.exp_zero] at h
  linarith

lemma mu_Ioi_one : expMeasure (1 : ℝ) (Set.Ioi 1) ≠ 0 := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, mu_Iic 1 zero_le_one]
  intro h
  have h1 : ENNReal.ofReal (1 - Real.exp (-1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have := Real.exp_pos (-1)
    linarith
  exact (tsub_pos_of_lt h1).ne' h

lemma mu_countable {D : Set ℝ} (hD : D.Countable) : expMeasure (1 : ℝ) D = 0 := by
  change (volume.withDensity (gammaPDF 1 1)) D = 0
  exact withDensity_absolutelyContinuous _ _ (hD.measure_zero volume)

lemma good_ae : ∀ᵐ ω ∂P0, ∀ i, 0 < ω i := by
  refine ae_all_iff.2 fun i => ?_
  rw [ae_iff]
  have : {ω : Ω0 | ¬ 0 < ω i} = T0 i ⁻¹' Set.Iic 0 := by
    ext ω
    simp [T0]
  rw [this, ← Measure.map_apply (T0_meas i) measurableSet_Iic, hT0.law i]
  exact mu_Iic_zero

lemma pair : IsMarkdownPair 2 1 1 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Measure

/-! ## Every admissible switching time sells nothing before switching -/

section Main

variable {τ : Ω0 → ℝ} (hτ : IsAdmissible P0 T0 1 1 τ)
include hτ

lemma tau_meas : Measurable τ :=
  measurable_of_Iic fun v => history_le T0 T0_meas v _ (hτ.stopping v)

lemma pathdet (v : ℝ) (ω ω' : Ω0)
    (h : ∀ u ∈ Set.Icc (0 : ℝ) v, countingProcess T0 u ω = countingProcess T0 u ω') :
    τ ω ≤ v ↔ τ ω' ≤ v := by
  obtain ⟨D, -, hDs, hD⟩ := history_det T0 v (hτ.stopping v)
  exact hD ω ω' fun u hu => h u (hDs hu)

lemma K1 {ω : Ω0} (hω : ∀ i, 0 < ω i) (hlt : τ ω < ω 0 + ω 1) : τ ω = τ (ws (ω 0)) := by
  have hagree : ∀ v, v < ω 0 + ω 1 → v ≤ 1 → (τ ω ≤ v ↔ τ (ws (ω 0)) ≤ v) := by
    intro v hv hv1
    refine pathdet hτ v _ _ fun u hu => ?_
    rw [cnt_good hω (lt_of_le_of_lt hu.2 hv), cnt_ws (hω 0) (by linarith [hu.2, hω 0])]
  have h1 := hτ.le_horizon ω
  have h2 := hτ.le_horizon (ws (ω 0))
  rcases lt_trichotomy (τ ω) (τ (ws (ω 0))) with h | h | h
  · exact absurd ((hagree _ hlt h1).1 le_rfl) (not_le.2 h)
  · exact h
  · exact absurd ((hagree _ (h.trans hlt) h2).2 le_rfl) (not_le.2 h)

lemma K2 {ω : Ω0} (hω : ∀ i, 0 < ω i) (hρ : ω 0 + ω 1 ≤ τ (ws (ω 0))) : ω 0 + ω 1 ≤ τ ω := by
  by_contra h
  rw [not_le] at h
  have := K1 hτ hω h
  linarith

lemma K3 {s v s'' : ℝ} (hs : 0 < s) (hQ : τ (ws s) = s) (hsv : s < v) (D : Set ℝ)
    (hDs : D ⊆ Set.Icc 0 v)
    (hD : ∀ ω ω', (∀ u ∈ D, countingProcess T0 u ω = countingProcess T0 u ω') →
      (ω ∈ {ω | τ ω ≤ v} ↔ ω' ∈ {ω | τ ω ≤ v}))
    (hsD : s ∉ D) (hv : v < s'') : τ (ws s'') ≤ v := by
  have hsp : τ (sp s) ≤ s := by
    refine (pathdet hτ s (ws s) (sp s) fun u hu => ?_).1 hQ.le
    rw [cnt_ws hs (by linarith [hu.2]), cnt_sp]
    by_cases hus : u = s
    · simp [hus]
    · have : ¬ s ≤ u := fun h => hus (le_antisymm hu.2 h)
      simp [hus, this]
  have hu' : ∀ u ∈ D, countingProcess T0 u (sp s) = countingProcess T0 u (ws s'') := by
    intro u hu
    have hu2 := hDs hu
    have hne : u ≠ s := fun h => hsD (h ▸ hu)
    rw [cnt_sp, cnt_ws (hs.trans (hsv.trans hv)) (by linarith [hu2.2]), if_neg hne,
      if_neg (not_le.2 (lt_of_le_of_lt hu2.2 hv))]
  exact (hD (sp s) (ws s'') hu').1 (hsp.trans hsv.le)

lemma mu_Q : expMeasure (1 : ℝ) {s | 0 < s ∧ τ (ws s) = s} = 0 := by
  set μ := expMeasure (1 : ℝ) with hμ
  set Q := {s : ℝ | 0 < s ∧ τ (ws s) = s} with hQdef
  by_contra hQ0
  set S := {v : ℝ | 0 < μ (Q ∩ Set.Iio v)} with hSdef
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hQ0
    have : Q = ⋃ m : ℕ, Q ∩ Set.Iio (m : ℝ) := by
      ext s
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iio]
      exact ⟨fun h => let ⟨m, hm⟩ := exists_nat_gt s; ⟨m, h, hm⟩, fun ⟨_, h, _⟩ => h⟩
    rw [this]
    refine measure_iUnion_null fun m => ?_
    have : (m : ℝ) ∉ S := by rw [hne]; exact Set.notMem_empty _
    simpa [S, pos_iff_ne_zero] using this
  have hSbdd : BddBelow S := ⟨0, fun v hv => by
    by_contra h
    rw [not_le] at h
    have : Q ∩ Set.Iio v = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hsv
      have := hs.1
      linarith
    have hv' : 0 < μ (Q ∩ Set.Iio v) := hv
    rw [this, measure_empty] at hv'
    exact lt_irrefl _ hv'⟩
  set q0 := sInf S with hq0
  have hbelow : ∀ v < q0, μ (Q ∩ Set.Iio v) = 0 := fun v hv => by
    have := notMem_of_lt_csInf hv hSbdd
    simpa [S, pos_iff_ne_zero] using this
  have hIio : μ (Q ∩ Set.Iio q0) = 0 := by
    have : Q ∩ Set.Iio q0 = ⋃ k : ℕ, Q ∩ Set.Iio (q0 - 1 / ((k : ℝ) + 1)) := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_iUnion]
      constructor
      · rintro ⟨hs, hsq⟩
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hsq)
        exact ⟨k, hs, by linarith⟩
      · rintro ⟨k, hs, hsk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact ⟨hs, by linarith⟩
    rw [this]
    exact measure_iUnion_null fun k => hbelow _
      (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith)
  have hIic : μ (Q ∩ Set.Iic q0) = 0 := by
    refine measure_mono_null (t := (Q ∩ Set.Iio q0) ∪ {q0}) ?_
      (measure_union_null hIio (mu_countable (Set.countable_singleton _)))
    rintro s ⟨hs, hsq⟩
    rcases (Set.mem_Iic.1 hsq).lt_or_eq with h | h
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr h
  have hIoi : μ (Q ∩ Set.Ioi q0) ≠ 0 := by
    intro h
    apply hQ0
    refine measure_mono_null (t := (Q ∩ Set.Iic q0) ∪ (Q ∩ Set.Ioi q0)) ?_
      (measure_union_null hIic h)
    intro s hs
    rcases le_or_gt s q0 with h' | h'
    · exact Or.inl ⟨hs, h'⟩
    · exact Or.inr ⟨hs, h'⟩
  obtain ⟨s'', hs''Q, hs''q⟩ := nonempty_of_measure_ne_zero hIoi
  rw [Set.mem_Ioi] at hs''q
  have hq0v : q0 < (q0 + s'') / 2 := by linarith
  have hvs'' : (q0 + s'') / 2 < s'' := by linarith
  set v := (q0 + s'') / 2 with hv
  obtain ⟨e, heS, hev⟩ := exists_lt_of_csInf_lt hSne hq0v
  have hv_pos : μ (Q ∩ Set.Iio v) ≠ 0 :=
    (lt_of_lt_of_le heS (measure_mono (Set.inter_subset_inter_right _
      (Set.Iio_subset_Iio hev.le)))).ne'
  obtain ⟨D, hDc, hDs, hD⟩ := history_det T0 v (hτ.stopping v)
  have hdiff : μ ((Q ∩ Set.Iio v) \ D) ≠ 0 := by
    intro h
    apply hv_pos
    refine measure_mono_null (t := ((Q ∩ Set.Iio v) \ D) ∪ D) ?_
      (measure_union_null h (mu_countable hDc))
    intro s hs
    by_cases hsD : s ∈ D
    · exact Or.inr hsD
    · exact Or.inl ⟨hs, hsD⟩
  obtain ⟨s, ⟨hsQ, hsv⟩, hsD⟩ := nonempty_of_measure_ne_zero hdiff
  have := K3 hτ hsQ.1 hsQ.2 hsv D hDs hD hsD hvs''
  rw [hs''Q.2] at this
  linarith

lemma mu_R (k : ℕ) :
    expMeasure (1 : ℝ) {s | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} = 0 := by
  have : IsProbabilityMeasure P0 := P0_prob
  set R := {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} with hRdef
  have hρ : Measurable fun s => τ (ws s) := (tau_meas hτ).comp measurable_ws
  have hRm : MeasurableSet R :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le (measurable_id.add_const _) hρ)
  by_contra hR
  set c : ℝ := 1 / ((k : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  set t : ℕ → Set ℝ := fun i => if i = 0 then R else if i = 1 then Set.Ioc 0 c else Set.Ioi 1
    with htdef
  have hEv : P0 (Set.pi (↑({0, 1, 2} : Finset ℕ)) t) ≠ 0 := by
    have hmt : ∀ i ∈ ({0, 1, 2} : Finset ℕ), MeasurableSet (t i) := by
      intro i _
      simp only [htdef]
      split_ifs
      · exact hRm
      · exact measurableSet_Ioc
      · exact measurableSet_Ioi
    unfold P0
    rw [Measure.infinitePi_pi _ hmt]
    simp only [htdef, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
      Finset.prod_singleton]
    norm_num
    exact ⟨hR, mu_Ioc hc, mu_Ioi_one⟩
  apply hEv
  refine measure_mono_null ?_ (measure_union_null (ae_iff.1 good_ae) (ae_iff.1 hτ.stock))
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_cases hpos : ∀ i, 0 < ω i
  swap
  · exact Or.inl hpos
  right
  have h0 : ω 0 ∈ R := by simpa [htdef] using hω 0 (by simp)
  have h1 : ω 1 ∈ Set.Ioc 0 c := by simpa [htdef] using hω 1 (by simp)
  have h2 : ω 2 ∈ Set.Ioi 1 := by simpa [htdef] using hω 2 (by simp)
  have hS2 : ω 0 + ω 1 ≤ τ ω := K2 hτ hpos (by linarith [h0.2, h1.2])
  have hτ1 := hτ.le_horizon ω
  have h3 : ∀ n, 3 ≤ n → τ ω < arrivalTime T0 n ω := by
    intro n hn
    have := (arr_mono hpos).monotone hn
    rw [arr_three] at this
    simp only [Set.mem_Ioi] at h2
    linarith [hpos 0, hpos 1]
  rw [cnt_two (by rw [arr_one]; linarith [hpos 1]) (by rw [arr_two]; exact hS2) h3]
  norm_num

lemma ae_cnt_zero : ∀ᵐ ω ∂P0, countingProcess T0 (τ ω) ω = 0 := by
  have : IsProbabilityMeasure P0 := P0_prob
  have hQ : ∀ᵐ ω ∂P0, ω 0 ∉ {s : ℝ | 0 < s ∧ τ (ws s) = s} := by
    rw [ae_iff]
    simp only [not_not]
    apply nonpos_iff_eq_zero.1
    calc P0 {ω | ω 0 ∈ {s : ℝ | 0 < s ∧ τ (ws s) = s}}
        = P0 (T0 0 ⁻¹' {s : ℝ | 0 < s ∧ τ (ws s) = s}) := rfl
      _ ≤ P0.map (T0 0) {s : ℝ | 0 < s ∧ τ (ws s) = s} :=
          Measure.le_map_apply (T0_meas 0).aemeasurable _
      _ = 0 := by rw [hT0.law 0]; exact mu_Q hτ
  have hR : ∀ᵐ ω ∂P0, ∀ k : ℕ, ω 0 ∉ {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} := by
    refine ae_all_iff.2 fun k => ?_
    rw [ae_iff]
    simp only [not_not]
    apply nonpos_iff_eq_zero.1
    calc P0 {ω | ω 0 ∈ {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)}}
        = P0 (T0 0 ⁻¹' {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)}) := rfl
      _ ≤ P0.map (T0 0) {s : ℝ | 0 < s ∧ s + 1 / ((k : ℝ) + 1) ≤ τ (ws s)} :=
          Measure.le_map_apply (T0_meas 0).aemeasurable _
      _ = 0 := by rw [hT0.law 0]; exact mu_R hτ k
  filter_upwards [good_ae, hτ.stock, hQ, hR] with ω hpos hst hq hr
  by_contra hne
  have h1 : countingProcess T0 (τ ω) ω = 1 := by omega
  have hlt : τ ω < ω 0 + ω 1 := by
    by_contra h
    rw [not_lt] at h
    exact cnt_ne_one hpos (by rw [arr_two]; exact h) h1
  have hge : ω 0 ≤ τ ω := by
    by_contra h
    rw [not_le] at h
    rw [cnt_good hpos hlt, if_neg (not_le.2 h)] at h1
    exact zero_ne_one h1
  have heq := K1 hτ hpos hlt
  rcases hge.lt_or_eq with h | h
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact hr k ⟨hpos 0, by rw [← heq]; linarith⟩
  · exact hq ⟨hpos 0, heq.symm.trans h.symm⟩

end Main

/-! ## Values -/

lemma J1_eq {u : ℝ} (hu : 0 ≤ u) :
    switchRevenue 2 1 1 3 1 u 0 = 1 - Real.exp (-(3 * u)) := by
  have h3 : (0 : ℝ) ≤ 3 * u := by positivity
  simp [switchRevenue, expMinPoisson, poissonTail, poissonPMFReal, Real.coe_toNNReal _ h3]

lemma G1_eq {s : ℝ} (hs : 0 ≤ s) : G 2 1 1 3 1 s = 1 - 2 * Real.exp (-(3 * s)) := by
  have h3 : (0 : ℝ) ≤ 3 * s := by positivity
  simp [G, poissonTail, poissonPMFReal, Real.coe_toNNReal _ h3]
  ring

lemma payoff_le {τ : Ω0 → ℝ} (hτ : IsAdmissible P0 T0 1 1 τ) :
    ∫ ω, (2 * ((min 1 (countingProcess T0 (τ ω) ω) : ℕ) : ℝ)
      + switchRevenue 2 1 1 3 (1 - countingProcess T0 (τ ω) ω) (1 - τ ω) 0) ∂P0
      ≤ switchRevenue 2 1 1 3 1 1 0 := by
  have : IsProbabilityMeasure P0 := P0_prob
  have hae : (fun ω => 2 * ((min 1 (countingProcess T0 (τ ω) ω) : ℕ) : ℝ)
      + switchRevenue 2 1 1 3 (1 - countingProcess T0 (τ ω) ω) (1 - τ ω) 0)
      =ᵐ[P0] fun ω => 1 - Real.exp (-(3 * (1 - τ ω))) := by
    filter_upwards [ae_cnt_zero hτ] with ω h
    rw [h, Nat.sub_zero, J1_eq (by linarith [hτ.le_horizon ω])]
    simp
  rw [integral_congr_ae hae, J1_eq zero_le_one]
  calc ∫ ω, (1 - Real.exp (-(3 * (1 - τ ω)))) ∂P0
      ≤ ∫ _ω, (1 - Real.exp (-(3 * 1))) ∂P0 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (integrable_const _) (Filter.Eventually.of_forall fun ω => ?_)
        · have := hτ.le_horizon ω
          simp only [Pi.zero_apply, sub_nonneg]
          exact Real.exp_le_one_iff.2 (by linarith)
        · have := hτ.nonneg ω
          simp only
          have : Real.exp (-(3 * (1 - τ ω))) ≥ Real.exp (-(3 * 1)) :=
            Real.exp_le_exp.2 (by linarith)
          linarith
    _ = 1 - Real.exp (-(3 * 1)) := by simp

lemma opt_le : optRevenue P0 T0 2 1 1 3 1 1 ≤ switchRevenue 2 1 1 3 1 1 0 := by
  unfold optRevenue stopValue
  refine Real.iSup_le (fun τ => payoff_le τ.2) ?_
  rw [J1_eq zero_le_one]
  have := Real.exp_le_one_iff.2 (by norm_num : -(3 * (1 : ℝ)) ≤ 0)
  linarith

lemma H_pos (H1 : ℝ → ℝ) (x1 : ℝ) (hx1 : x1 = Real.log 2 / 3)
    (hd : ∀ t, 0 < t → HasDerivAt H1 (-H1 t + (1 - 2 * Real.exp (-(3 * t)))) t)
    (hH : H1 x1 = 0) : 0 < H1 1 := by
  have hφ : ∀ t, 0 < t → HasDerivAt (fun t => Real.exp t * H1 t)
      (Real.exp t * (1 - 2 * Real.exp (-(3 * t)))) t := by
    intro t ht
    have h := (Real.hasDerivAt_exp t).mul (hd t ht)
    have he : Real.exp t * H1 t + Real.exp t * (-H1 t + (1 - 2 * Real.exp (-(3 * t))))
        = Real.exp t * (1 - 2 * Real.exp (-(3 * t))) := by ring
    rw [he] at h
    exact h
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hx1pos : 0 < x1 := by rw [hx1]; positivity
  have hx1lt : x1 < 1 := by
    rw [hx1]
    have := Real.log_two_lt_d9
    linarith
  have hmono : StrictMonoOn (fun t => Real.exp t * H1 t) (Set.Icc x1 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
    · intro t ht
      exact (hφ t (hx1pos.trans_le ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφ t (hx1pos.trans ht.1)).deriv]
      apply mul_pos (Real.exp_pos _)
      have : Real.exp (-(3 * t)) < 1 / 2 := by
        rw [show (1 : ℝ) / 2 = Real.exp (-Real.log 2) by
          rw [Real.exp_neg, Real.exp_log two_pos]; norm_num]
        exact Real.exp_lt_exp.2 (by rw [hx1] at ht; linarith [ht.1])
      linarith
  have := hmono ⟨le_rfl, hx1lt.le⟩ ⟨hx1lt.le, le_rfl⟩ hx1lt
  simp only [hH, mul_zero] at this
  exact pos_of_mul_pos_right this (Real.exp_pos 1).le

end DP872

open PriceSwitch.Markdown MeasureTheory QueueingFundamentals.Foundations in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ)
    (p₁ lam₁ p₂ lam₂ : ℝ) (hpair : IsMarkdownPair p₁ lam₁ p₂ lam₂)
    (hT : IsExpInterarrivals P lam₁ T),
    ∃ (x : ℕ → ℝ) (F H : ℕ → ℝ → ℝ),
      StrictMonoOn x (Set.Ici 1) ∧
      (∀ t, F 0 t = 0) ∧
      (∀ n, 1 ≤ n →
        (∀ t, 0 < t → HasDerivAt (H n)
          (-lam₁ * H n t + G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t) t) ∧
        H n (x n) = 0 ∧
        (∃ t, 0 ≤ t ∧ G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0) ∧
        x n = sInf {t : ℝ | 0 ≤ t ∧
          G p₁ lam₁ p₂ lam₂ n t + lam₁ * F (n - 1) t = 0} ∧
        (∀ t, F n t = if t < x n then 0 else H n t)) ∧
      x 1 = sInf {s : ℝ | 0 ≤ s ∧ G p₁ lam₁ p₂ lam₂ 1 s = 0} ∧
      (∀ n, 1 < n → x n < sInf {s : ℝ | 0 ≤ s ∧ G p₁ lam₁ p₂ lam₂ n s = 0}) ∧
      (∀ n, 1 ≤ n → ∀ t, 0 ≤ t →
        optRevenue P T p₁ lam₁ p₂ lam₂ n t =
          if t ≤ x n then switchRevenue p₁ lam₁ p₂ lam₂ n t 0
          else switchRevenue p₁ lam₁ p₂ lam₂ n t 0 + F n t)) := by
  intro h
  obtain ⟨x, F, H, -, hF0, hn, -, -, hval⟩ :=
    @h DP872.Ω0 _ DP872.P0 DP872.P0_prob DP872.T0 2 1 1 3 DP872.pair DP872.hT0
  obtain ⟨hd, hHx, -, hxeq, hFd⟩ := hn 1 le_rfl
  have hsub : (1 : ℕ) - 1 = 0 := rfl
  have hset : {t : ℝ | 0 ≤ t ∧ G 2 1 1 3 1 t + 1 * F (1 - 1) t = 0} = {Real.log 2 / 3} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ht, h⟩
      rw [hsub, hF0, DP872.G1_eq ht] at h
      have h2 : Real.exp (-(3 * t)) = 1 / 2 := by linarith
      have := congrArg Real.log h2
      rw [Real.log_exp, one_div, Real.log_inv] at this
      linarith
    · rintro rfl
      refine ⟨div_nonneg (Real.log_nonneg one_le_two) (by norm_num), ?_⟩
      rw [hsub, hF0, DP872.G1_eq (div_nonneg (Real.log_nonneg one_le_two) (by norm_num))]
      rw [show -(3 * (Real.log 2 / 3)) = -Real.log 2 by ring, Real.exp_neg,
        Real.exp_log two_pos]
      norm_num
  rw [hset, csInf_singleton] at hxeq
  have hx1lt : x 1 < 1 := by
    rw [hxeq]
    have := Real.log_two_lt_d9
    linarith
  have hd' : ∀ t, 0 < t → HasDerivAt (H 1) (-H 1 t + (1 - 2 * Real.exp (-(3 * t)))) t := by
    intro t ht
    convert hd t ht using 1
    rw [hsub, hF0, DP872.G1_eq ht.le]
    ring
  have hHpos := DP872.H_pos (H 1) (x 1) hxeq hd' hHx
  have hopt := hval 1 le_rfl 1 zero_le_one
  rw [if_neg (not_le.2 hx1lt), hFd 1, if_neg (not_lt.2 hx1lt.le)] at hopt
  have hle := DP872.opt_le
  linarith
