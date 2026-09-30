-- Prove2me | solution 1 for UnderstandingML.stumps_weakly_learn_three_piece
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:21:13.849078+00:00
-- url     : https://prove2.me/submissions/796bab81-0286-4010-ae16-a211689f169e

import Definitions.Def_UnderstandingML_Boosting
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real


open MeasureTheory ProbabilityTheory

namespace UnderstandingML

section Chebyshev

variable {Z : Type*} [MeasurableSpace Z]

/-- The empirical frequency of a set `E` in the sample `S`. -/
noncomputable def empFreq {m : ℕ} (S : Fin m → Z) (E : Set Z) : ℝ :=
  (∑ i, E.indicator (fun _ ↦ (1 : ℝ)) (S i)) / m

/-- Chebyshev's inequality for the empirical frequency of a single event under `D^m`. -/
lemma iidLaw_empFreq_dev_le (P : Measure Z) [IsProbabilityMeasure P] {E : Set Z}
    (hE : MeasurableSet E) {m : ℕ} (hm : 0 < m) {η : ℝ} (hη : 0 < η) :
    iidLaw P m {S | η ≤ |empFreq S E - P.real E|} ≤ ENNReal.ofReal (1 / (4 * m * η ^ 2)) := by
  set μ : Measure (Fin m → Z) := Measure.pi fun _ ↦ P with hμ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let g : Z → ℝ := E.indicator fun _ ↦ (1 : ℝ)
  have hg : Measurable g := measurable_const.indicator hE
  let X : Fin m → (Fin m → Z) → ℝ := fun i S ↦ g (S i)
  have hXm : ∀ i, Measurable (X i) := fun i ↦ hg.comp (measurable_pi_apply i)
  have hXb : ∀ i S, X i S ∈ Set.Icc (0 : ℝ) 1 := by
    intro i S
    simp only [X, g, Set.indicator]
    split_ifs <;> simp
  have hXL : ∀ i, MemLp (X i) 2 μ := by
    intro i
    refine MemLp.of_bound (hXm i).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun S ↦ ?_)
    have := hXb i S
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hind : iIndepFun X μ := by
    have := iIndepFun_pi (μ := fun _ : Fin m ↦ P) (X := fun _ : Fin m ↦ g)
      (fun _ ↦ hg.aemeasurable)
    exact this
  let Y : (Fin m → Z) → ℝ := ∑ i, X i
  have hYL : MemLp Y 2 μ := memLp_finset_sum' _ fun i _ ↦ hXL i
  have hvar : Var[Y; μ] ≤ m / 4 := by
    have hsum := IndepFun.variance_sum (μ := μ) (X := X) (s := Finset.univ)
      (fun i _ ↦ hXL i) (fun i _ j _ hij ↦ hind.indepFun hij)
    have : Var[Y; μ] = ∑ i, Var[X i; μ] := hsum
    rw [this]
    calc ∑ i, Var[X i; μ] ≤ ∑ _i : Fin m, (1 / 4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have h1 := variance_le_sub_mul_sub (μ := μ) (a := 0) (b := 1) (X := X i)
            (Filter.Eventually.of_forall (hXb i)) (hXm i).aemeasurable
          nlinarith [sq_nonneg (∫ x, X i x ∂μ - 1 / 2)]
      _ = m / 4 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hint : ∫ S, Y S ∂μ = m * P.real E := by
    have hi : ∀ i, ∫ S, X i S ∂μ = P.real E := by
      intro i
      have hmp := measurePreserving_eval (fun _ : Fin m ↦ P) i
      calc ∫ S, X i S ∂μ = ∫ z, g z ∂(μ.map (Function.eval i)) := by
            rw [integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]
            try rfl
        _ = ∫ z, g z ∂P := by rw [hmp.map_eq]
        _ = P.real E := integral_indicator_one hE
    have : ∫ S, Y S ∂μ = ∑ i, ∫ S, X i S ∂μ := by
      simp only [Y, Finset.sum_apply]
      exact integral_finset_sum _ fun i _ ↦ (hXL i).integrable one_le_two
    rw [this, Finset.sum_congr rfl fun i _ ↦ hi i]
    simp
  have hcheb := meas_ge_le_variance_div_sq hYL (c := m * η) (by positivity)
  have hsub : {S : Fin m → Z | η ≤ |empFreq S E - P.real E|} ⊆
      {S | m * η ≤ |Y S - ∫ S, Y S ∂μ|} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    rw [hint]
    have hY : Y S = ∑ i, E.indicator (fun _ ↦ (1 : ℝ)) (S i) := by
      simp [Y, X, g, Finset.sum_apply]
    have : Y S - m * P.real E = m * (empFreq S E - P.real E) := by
      rw [hY, empFreq]; field_simp
    rw [this, abs_mul, abs_of_pos hmR]
    exact mul_le_mul_of_nonneg_left hS hmR.le
  calc iidLaw P m {S | η ≤ |empFreq S E - P.real E|}
      ≤ μ {S | m * η ≤ |Y S - ∫ S, Y S ∂μ|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Var[Y; μ] / (m * η) ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (1 / (4 * m * η ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hvar]

end Chebyshev

end UnderstandingML

open MeasureTheory Set Filter Topology

namespace UnderstandingML

section MeasureLimits

variable {α : Type*} [MeasurableSpace α]

lemma measureReal_iInter_ge (μ : Measure α) [IsFiniteMeasure μ] {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (hmono : Antitone s) {a : ℝ}
    (ha : ∀ n, a ≤ μ.real (s n)) : a ≤ μ.real (⋂ n, s n) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ (hs n).nullMeasurableSet) hmono
    ⟨0, measure_ne_top _ _⟩
  have ht' : Tendsto (fun n ↦ μ.real (s n)) atTop (𝓝 (μ.real (⋂ n, s n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto' ht' ha

lemma measureReal_iUnion_le (μ : Measure α) [IsFiniteMeasure μ] {s : ℕ → Set α}
    (hmono : Monotone s) {a : ℝ} (ha : ∀ n, μ.real (s n) ≤ a) : μ.real (⋃ n, s n) ≤ a := by
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have ht' : Tendsto (fun n ↦ μ.real (s n)) atTop (𝓝 (μ.real (⋃ n, s n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact le_of_tendsto' ht' ha

lemma exists_measureReal_lt_of_iInter_empty (μ : Measure α) [IsFiniteMeasure μ]
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) (hmono : Antitone s)
    (hempty : (⋂ n, s n) = ∅) {ε : ℝ} (hε : 0 < ε) : ∃ n, μ.real (s n) < ε := by
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ (hs n).nullMeasurableSet) hmono
    ⟨0, measure_ne_top _ _⟩
  have ht' : Tendsto (fun n ↦ μ.real (s n)) atTop (𝓝 (μ.real (⋂ n, s n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  rw [hempty, measureReal_empty] at ht'
  exact (ht'.eventually (gt_mem_nhds hε)).exists

end MeasureLimits

section SubCDF

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

lemma measureReal_Iic_right {t a : ℝ} (h : ∀ θ, t < θ → a ≤ μ.real (Iic θ)) :
    a ≤ μ.real (Iic t) := by
  have hI : (⋂ n : ℕ, Iic (t + 1 / ((n : ℝ) + 1))) = Iic t := by
    ext x
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro hx
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      linarith [hx n]
    · intro hx n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [← hI]
  refine measureReal_iInter_ge μ (fun n ↦ measurableSet_Iic) ?_ fun n ↦ h _ ?_
  · intro n m hnm
    apply Iic_subset_Iic.2
    have : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    linarith
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma measureReal_Iio_le {t a : ℝ} (h : ∀ θ, θ < t → μ.real (Iic θ) ≤ a) :
    μ.real (Iio t) ≤ a := by
  have hI : (⋃ n : ℕ, Iic (t - 1 / ((n : ℝ) + 1))) = Iio t := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
  rw [← hI]
  refine measureReal_iUnion_le μ ?_ fun n ↦ h _ ?_
  · intro n m hnm
    apply Iic_subset_Iic.2
    have : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    linarith
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma measureReal_univ_le_of_Iic {a : ℝ} (h : ∀ θ, μ.real (Iic θ) ≤ a) :
    μ.real univ ≤ a := by
  have hI : (⋃ n : ℕ, Iic (n : ℝ)) = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, hn⟩
  rw [← hI]
  refine measureReal_iUnion_le μ ?_ fun n ↦ h _
  intro n m hnm
  exact Iic_subset_Iic.2 (by exact_mod_cast hnm)

lemma exists_measureReal_Iic_lt {ε : ℝ} (hε : 0 < ε) : ∃ θ, μ.real (Iic θ) < ε := by
  obtain ⟨n, hn⟩ := exists_measureReal_lt_of_iInter_empty μ
    (s := fun n : ℕ ↦ Iic (-(n : ℝ))) (fun n ↦ measurableSet_Iic)
    (fun n m hnm ↦ Iic_subset_Iic.2 (by simp only [neg_le_neg_iff]; exact_mod_cast hnm))
    (by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩) hε
  exact ⟨_, hn⟩

lemma exists_measureReal_Ioo_lt (θ₁ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ < θ₁, μ.real (Ioo θ θ₁) < ε := by
  obtain ⟨n, hn⟩ := exists_measureReal_lt_of_iInter_empty μ
    (s := fun n : ℕ ↦ Ioo (θ₁ - 1 / ((n : ℝ) + 1)) θ₁) (fun n ↦ measurableSet_Ioo)
    (by
      intro n m hnm
      apply Ioo_subset_Ioo_left
      have : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hnm 1
      linarith)
    (by
      ext x
      simp only [mem_iInter, mem_Ioo, mem_empty_iff_false, iff_false, not_forall]
      by_cases hx : x < θ₁
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨n, fun h ↦ by linarith [h.1]⟩
      · exact ⟨0, fun h ↦ hx h.2⟩) hε
  refine ⟨_, ?_, hn⟩
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma exists_measureReal_Ioi_lt (θ₂ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ, θ₂ ≤ θ ∧ μ.real (Ioi θ) < ε := by
  obtain ⟨n, hn⟩ := exists_measureReal_lt_of_iInter_empty μ
    (s := fun n : ℕ ↦ Ioi (θ₂ + n)) (fun n ↦ measurableSet_Ioi)
    (fun n m hnm ↦ Ioi_subset_Ioi (by simp only [add_le_add_iff_left]; exact_mod_cast hnm))
    (by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge (x - θ₂)
      exact ⟨n, by linarith⟩) hε
  exact ⟨_, by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], hn⟩

end SubCDF

/-- **Bracketing.** For a finite measure `μ` on `ℝ` of mass at most `1` and `η > 0`, there are at
most `2k + 2` sets (with `k η ≥ 1`) that bracket every half-line `(-∞, θ]` from inside and outside
up to mass `η`. -/
lemma bracket_Iic (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ.real univ ≤ 1) {η : ℝ}
    (hη : 0 < η) (k : ℕ) (hk : 1 ≤ k * η) :
    ∃ 𝓐 : Finset (Set ℝ), 𝓐.card ≤ 2 * k + 2 ∧ (∀ A ∈ 𝓐, MeasurableSet A) ∧
      ∀ θ : ℝ, ∃ A ∈ 𝓐, ∃ A' ∈ 𝓐, A ⊆ Iic θ ∧ Iic θ ⊆ A' ∧ μ.real A' ≤ μ.real A + η := by
  classical
  set F : ℝ → ℝ := fun θ ↦ μ.real (Iic θ) with hF
  have hFmono : Monotone F := fun a b hab ↦ measureReal_mono (Iic_subset_Iic.2 hab)
  let Sj : ℕ → Set ℝ := fun j ↦ {θ | j * η ≤ F θ}
  let t : ℕ → ℝ := fun j ↦ sInf (Sj j)
  obtain ⟨θ0, hθ0⟩ := exists_measureReal_Iic_lt μ hη
  have hbdd : ∀ j, 1 ≤ j → BddBelow (Sj j) := by
    intro j hj
    refine ⟨θ0, fun θ hθ ↦ ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 := hFmono hlt.le
    have h2 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h3 : (j : ℝ) * η ≤ F θ := hθ
    have h4 : F θ0 < η := hθ0
    nlinarith
  have ht_le : ∀ j θ, 1 ≤ j → θ ∈ Sj j → t j ≤ θ := fun j θ hj hθ ↦ csInf_le (hbdd j hj) hθ
  have ht_mem : ∀ j, (Sj j).Nonempty → j * η ≤ F (t j) := by
    intro j hne
    apply measureReal_Iic_right μ
    intro θ hθ
    obtain ⟨θ', hθ'S, hθ'lt⟩ := exists_lt_of_csInf_lt hne hθ
    exact le_trans hθ'S (hFmono hθ'lt.le)
  have hIio : ∀ j, 1 ≤ j → μ.real (Iio (t j)) ≤ j * η := by
    intro j hj
    apply measureReal_Iio_le μ
    intro θ hθ
    by_contra hcon
    push Not at hcon
    have : t j ≤ θ := ht_le j θ hj hcon.le
    linarith
  let 𝓐 : Finset (Set ℝ) := ({∅, univ} ∪ (Finset.range k).image fun j ↦ Iic (t (j + 1))) ∪
    (Finset.range k).image fun j ↦ Iio (t (j + 1))
  have hIic_mem : ∀ j, 1 ≤ j → j ≤ k → Iic (t j) ∈ 𝓐 := by
    intro j hj1 hjk
    simp only [𝓐, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    refine Or.inl (Or.inr ⟨j - 1, by omega, ?_⟩)
    rw [Nat.sub_add_cancel hj1]
  have hIio_mem : ∀ j, 1 ≤ j → j ≤ k → Iio (t j) ∈ 𝓐 := by
    intro j hj1 hjk
    simp only [𝓐, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    refine Or.inr ⟨j - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hj1]
  have hempty_mem : (∅ : Set ℝ) ∈ 𝓐 := by simp [𝓐]
  have huniv_mem : (univ : Set ℝ) ∈ 𝓐 := by simp [𝓐]
  refine ⟨𝓐, ?_, ?_, ?_⟩
  · calc 𝓐.card ≤ ({∅, univ} ∪ (Finset.range k).image fun j ↦ Iic (t (j + 1))).card +
          ((Finset.range k).image fun j ↦ Iio (t (j + 1))).card := Finset.card_union_le _ _
      _ ≤ (({∅, univ} : Finset (Set ℝ)).card +
          ((Finset.range k).image fun j ↦ Iic (t (j + 1))).card) + k := by
          gcongr
          · exact Finset.card_union_le _ _
          · exact (Finset.card_image_le).trans (by simp)
      _ ≤ (2 + k) + k := by
          gcongr
          · exact Finset.card_le_two
          · exact (Finset.card_image_le).trans (by simp)
      _ = 2 * k + 2 := by ring
  · intro A hA
    simp only [𝓐, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range] at hA
    rcases hA with ((rfl | rfl) | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩
    · exact MeasurableSet.empty
    · exact MeasurableSet.univ
    · exact measurableSet_Iic
    · exact measurableSet_Iio
  · intro θ
    set j := ⌊F θ / η⌋₊ with hjdef
    have hF0 : 0 ≤ F θ := measureReal_nonneg
    have hj1 : (j : ℝ) * η ≤ F θ := by
      have := Nat.floor_le (div_nonneg hF0 hη.le)
      rwa [le_div_iff₀ hη] at this
    have hj2 : F θ < ((j : ℝ) + 1) * η := by
      have := Nat.lt_floor_add_one (F θ / η)
      rwa [div_lt_iff₀ hη] at this
    have hFθ1 : F θ ≤ 1 := (measureReal_mono (subset_univ _)).trans hμ
    have hjk : j ≤ k := by
      have : (j : ℝ) * η ≤ k * η := by linarith
      exact_mod_cast le_of_mul_le_mul_right this hη
    obtain ⟨A, hA𝓐, hAsub, hAval⟩ : ∃ A ∈ 𝓐, A ⊆ Iic θ ∧ (j : ℝ) * η ≤ μ.real A := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · refine ⟨∅, hempty_mem, empty_subset _, ?_⟩
        rw [h0]; simp
      · have hmem : θ ∈ Sj j := hj1
        exact ⟨Iic (t j), hIic_mem j hpos hjk, Iic_subset_Iic.2 (ht_le j θ hpos hmem),
          ht_mem j ⟨θ, hmem⟩⟩
    obtain ⟨A', hA'𝓐, hA'sup, hA'val⟩ :
        ∃ A' ∈ 𝓐, Iic θ ⊆ A' ∧ μ.real A' ≤ ((j : ℝ) + 1) * η := by
      by_cases hjk' : j < k
      · by_cases hne : (Sj (j + 1)).Nonempty
        · have hθlt : θ < t (j + 1) := by
            by_contra hcon
            push Not at hcon
            have h1 := ht_mem (j + 1) hne
            have h2 := hFmono hcon
            push_cast at h1
            linarith
          refine ⟨Iio (t (j + 1)), hIio_mem (j + 1) (by omega) (by omega),
            fun x hx ↦ lt_of_le_of_lt hx hθlt, ?_⟩
          have := hIio (j + 1) (by omega)
          push_cast at this
          exact this
        · refine ⟨univ, huniv_mem, subset_univ _, measureReal_univ_le_of_Iic μ fun θ' ↦ ?_⟩
          by_contra hcon
          push Not at hcon
          exact hne ⟨θ', by show ((j + 1 : ℕ) : ℝ) * η ≤ F θ'; push_cast; exact hcon.le⟩
      · refine ⟨univ, huniv_mem, subset_univ _, ?_⟩
        have hjk2 : j = k := le_antisymm hjk (not_lt.1 hjk')
        rw [hjk2]
        linarith
    exact ⟨A, hA𝓐, A', hA'𝓐, hAsub, hA'sup, by linarith⟩

end UnderstandingML

open MeasureTheory Set

namespace UnderstandingML

section StumpsUniform

/-- The set of labeled examples on which `h` errs. -/
def lossSet (h : ℝ → Bool) : Set (ℝ × Bool) := {z | h z.1 ≠ z.2}

/-- The restriction of a measure on labeled examples to one label, as a measure on `ℝ`. -/
noncomputable def slice (ν : Measure (ℝ × Bool)) (c : Bool) : Measure ℝ :=
  (ν.restrict (univ ×ˢ {c})).map Prod.fst

instance slice_isFinite (ν : Measure (ℝ × Bool)) [IsFiniteMeasure ν] (c : Bool) :
    IsFiniteMeasure (slice ν c) := by
  unfold slice
  infer_instance

lemma slice_real (ν : Measure (ℝ × Bool)) (c : Bool) {A : Set ℝ} (hA : MeasurableSet A) :
    (slice ν c).real A = ν.real (A ×ˢ {c}) := by
  rw [Measure.real, Measure.real, slice, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  congr 2
  ext z
  simp [and_comm]

lemma measureReal_lossSet_gt (ν : Measure (ℝ × Bool)) [IsFiniteMeasure ν] (θ : ℝ) :
    ν.real (lossSet fun x ↦ decide (θ < x)) = ν.real (Iic θ ×ˢ {true}) +
      (ν.real (univ ×ˢ {false}) - ν.real (Iic θ ×ˢ {false})) := by
  have hset : (lossSet fun x ↦ decide (θ < x)) =
      (Iic θ ×ˢ {true}) ∪ ((univ ×ˢ {false}) \ (Iic θ ×ˢ {false})) := by
    ext ⟨x, y⟩
    cases y <;> simp [lossSet]
  rw [hset, measureReal_union _ ((MeasurableSet.univ.prod (measurableSet_singleton _)).diff
      (measurableSet_Iic.prod (measurableSet_singleton _))),
    measureReal_diff (prod_mono (subset_univ _) subset_rfl)
      (measurableSet_Iic.prod (measurableSet_singleton _))]
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [mem_prod, mem_singleton_iff, mem_diff, mem_univ, true_and] at h1 h2
  rw [h1.2] at h2
  exact absurd h2.1 (by simp)

lemma measureReal_lossSet_le (ν : Measure (ℝ × Bool)) [IsFiniteMeasure ν] (θ : ℝ) :
    ν.real (lossSet fun x ↦ decide (x ≤ θ)) = ν.real (Iic θ ×ˢ {false}) +
      (ν.real (univ ×ˢ {true}) - ν.real (Iic θ ×ˢ {true})) := by
  have hset : (lossSet fun x ↦ decide (x ≤ θ)) =
      (Iic θ ×ˢ {false}) ∪ ((univ ×ˢ {true}) \ (Iic θ ×ˢ {true})) := by
    ext ⟨x, y⟩
    cases y <;> simp [lossSet]
  rw [hset, measureReal_union _ ((MeasurableSet.univ.prod (measurableSet_singleton _)).diff
      (measurableSet_Iic.prod (measurableSet_singleton _))),
    measureReal_diff (prod_mono (subset_univ _) subset_rfl)
      (measurableSet_Iic.prod (measurableSet_singleton _))]
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [mem_prod, mem_singleton_iff, mem_diff, mem_univ, true_and] at h1 h2
  rw [h1.2] at h2
  exact absurd h2.1 (by simp)

/-- **Uniform deviation over decision stumps.** Given a reference finite measure `ν₁` of mass at
most `1`, there is a family of at most `4k + 6` measurable sets such that any finite measure `ν₂`
close to `ν₁` on every set of the family is uniformly close to `ν₁` on the error sets of all
decision stumps. -/
lemma stump_uniform_bracket (ν₁ : Measure (ℝ × Bool)) [IsFiniteMeasure ν₁]
    (hν : ν₁.real univ ≤ 1) {η : ℝ} (hη : 0 < η) (k : ℕ) (hk : 1 ≤ k * η) :
    ∃ 𝓕 : Finset (Set (ℝ × Bool)), 𝓕.card ≤ 4 * k + 6 ∧ (∀ E ∈ 𝓕, MeasurableSet E) ∧
      ∀ ν₂ : Measure (ℝ × Bool), IsFiniteMeasure ν₂ →
        (∀ E ∈ 𝓕, |ν₂.real E - ν₁.real E| ≤ η) →
        ∀ h ∈ decisionStumps, |ν₂.real (lossSet h) - ν₁.real (lossSet h)| ≤ 5 * η := by
  classical
  have hslice_le : ∀ c, (slice ν₁ c).real univ ≤ 1 := by
    intro c
    rw [slice_real ν₁ c MeasurableSet.univ]
    exact (measureReal_mono (subset_univ _)).trans hν
  obtain ⟨𝓐T, hcT, hmT, hbT⟩ := bracket_Iic (slice ν₁ true) (hslice_le true) hη k hk
  obtain ⟨𝓐F, hcF, hmF, hbF⟩ := bracket_Iic (slice ν₁ false) (hslice_le false) hη k hk
  let 𝓕 : Finset (Set (ℝ × Bool)) :=
    ((𝓐T.image fun A ↦ A ×ˢ ({true} : Set Bool)) ∪ (𝓐F.image fun A ↦ A ×ˢ ({false} : Set Bool)))
      ∪ {univ ×ˢ {true}, univ ×ˢ {false}}
  have hT_mem : ∀ A ∈ 𝓐T, A ×ˢ ({true} : Set Bool) ∈ 𝓕 := fun A hA ↦ by
    simp only [𝓕, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨A, hA, rfl⟩)
  have hF_mem : ∀ A ∈ 𝓐F, A ×ˢ ({false} : Set Bool) ∈ 𝓕 := fun A hA ↦ by
    simp only [𝓕, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨A, hA, rfl⟩)
  have huniv_mem : ∀ c : Bool, (univ ×ˢ ({c} : Set Bool)) ∈ 𝓕 := by
    intro c
    cases c <;> simp [𝓕]
  refine ⟨𝓕, ?_, ?_, ?_⟩
  · calc 𝓕.card ≤ ((𝓐T.image fun A ↦ A ×ˢ ({true} : Set Bool)) ∪
          (𝓐F.image fun A ↦ A ×ˢ ({false} : Set Bool))).card +
          ({univ ×ˢ {true}, univ ×ˢ {false}} : Finset (Set (ℝ × Bool))).card :=
          Finset.card_union_le _ _
      _ ≤ ((𝓐T.image fun A ↦ A ×ˢ ({true} : Set Bool)).card +
          (𝓐F.image fun A ↦ A ×ˢ ({false} : Set Bool)).card) + 2 := by
          gcongr
          · exact Finset.card_union_le _ _
          · exact Finset.card_le_two
      _ ≤ ((2 * k + 2) + (2 * k + 2)) + 2 := by
          gcongr
          · exact Finset.card_image_le.trans hcT
          · exact Finset.card_image_le.trans hcF
      _ = 4 * k + 6 := by ring
  · intro E hE
    simp only [𝓕, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton] at hE
    rcases hE with (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) | rfl | rfl
    · exact (hmT A hA).prod (measurableSet_singleton _)
    · exact (hmF A hA).prod (measurableSet_singleton _)
    · exact MeasurableSet.univ.prod (measurableSet_singleton _)
    · exact MeasurableSet.univ.prod (measurableSet_singleton _)
  · intro ν₂ hν₂ hdev h hh
    -- deviation on half-lines of each label
    have key : ∀ (c : Bool) (𝓐 : Finset (Set ℝ)), (∀ A ∈ 𝓐, A ×ˢ ({c} : Set Bool) ∈ 𝓕) →
        (∀ A ∈ 𝓐, MeasurableSet A) →
        (∀ θ : ℝ, ∃ A ∈ 𝓐, ∃ A' ∈ 𝓐, A ⊆ Iic θ ∧ Iic θ ⊆ A' ∧
          (slice ν₁ c).real A' ≤ (slice ν₁ c).real A + η) →
        ∀ θ, |ν₂.real (Iic θ ×ˢ {c}) - ν₁.real (Iic θ ×ˢ {c})| ≤ 2 * η := by
      intro c 𝓐 hmem hmeas hbr θ
      obtain ⟨A, hA, A', hA', hAsub, hA'sup, hval⟩ := hbr θ
      rw [slice_real ν₁ c (hmeas A' hA'), slice_real ν₁ c (hmeas A hA)] at hval
      have d1 := abs_le.1 (hdev _ (hmem A hA))
      have d2 := abs_le.1 (hdev _ (hmem A' hA'))
      have m1 : ν₂.real (A ×ˢ {c}) ≤ ν₂.real (Iic θ ×ˢ {c}) :=
        measureReal_mono (prod_mono hAsub subset_rfl)
      have m2 : ν₂.real (Iic θ ×ˢ {c}) ≤ ν₂.real (A' ×ˢ {c}) :=
        measureReal_mono (prod_mono hA'sup subset_rfl)
      have m3 : ν₁.real (A ×ˢ {c}) ≤ ν₁.real (Iic θ ×ˢ {c}) :=
        measureReal_mono (prod_mono hAsub subset_rfl)
      have m4 : ν₁.real (Iic θ ×ˢ {c}) ≤ ν₁.real (A' ×ˢ {c}) :=
        measureReal_mono (prod_mono hA'sup subset_rfl)
      rw [abs_le]
      constructor <;> linarith [d1.1, d1.2, d2.1, d2.2]
    have kT := key true 𝓐T hT_mem hmT hbT
    have kF := key false 𝓐F hF_mem hmF hbF
    have uT := abs_le.1 (hdev _ (huniv_mem true))
    have uF := abs_le.1 (hdev _ (huniv_mem false))
    rcases hh with ⟨θ, rfl⟩ | ⟨θ, rfl⟩
    · rw [measureReal_lossSet_gt, measureReal_lossSet_gt]
      have a1 := abs_le.1 (kT θ)
      have a2 := abs_le.1 (kF θ)
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    · rw [measureReal_lossSet_le, measureReal_lossSet_le]
      have a1 := abs_le.1 (kT θ)
      have a2 := abs_le.1 (kF θ)
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

end StumpsUniform

end UnderstandingML

open MeasureTheory Set

namespace UnderstandingML

section StumpsWeak

/-- The empirical measure of a sample. -/
noncomputable def empMeasure {Z : Type*} [MeasurableSpace Z] {m : ℕ} (S : Fin m → Z) :
    Measure Z :=
  ((m : NNReal)⁻¹ : NNReal) • ∑ i, Measure.dirac (S i)

instance empMeasure_isFinite {Z : Type*} [MeasurableSpace Z] {m : ℕ} (S : Fin m → Z) :
    IsFiniteMeasure (empMeasure S) := by
  unfold empMeasure
  infer_instance

lemma empMeasure_real {Z : Type*} [MeasurableSpace Z] {m : ℕ} (S : Fin m → Z) {E : Set Z}
    (hE : MeasurableSet E) : (empMeasure S).real E = empFreq S E := by
  rw [Measure.real, empMeasure, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ hE]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_sum]
  · rw [empFreq, div_eq_inv_mul]
    have h1 : ((((m : NNReal)⁻¹ : NNReal) : ENNReal)).toReal = (m : ℝ)⁻¹ := by simp
    have h2 : ∑ a, (E.indicator 1 (S a) : ENNReal).toReal =
        ∑ i, E.indicator (fun _ ↦ (1 : ℝ)) (S i) :=
      Finset.sum_congr rfl fun i _ ↦ by by_cases h : S i ∈ E <;> simp [h]
    rw [h1, h2]
  · intro i _
    by_cases h : S i ∈ E <;> simp [h]

lemma measurableSet_lossSet {h : ℝ → Bool} (hh : Measurable h) : MeasurableSet (lossSet h) :=
  (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl

lemma empRisk_eq_empFreq {m : ℕ} (S : Fin m → ℝ × Bool) (h : ℝ → Bool) :
    empRisk loss01 S h = empFreq S (lossSet h) := by
  rw [empRisk, empFreq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [loss01, lossSet, Set.indicator, Set.mem_setOf_eq]
  split_ifs <;> simp_all

lemma trueError_eq_labeledLaw (D : Measure ℝ) {f h : ℝ → Bool} (hf : Measurable f)
    (hh : Measurable h) : trueError D f h = (labeledLaw D f).real (lossSet h) := by
  have hmeas : Measurable (fun x : ℝ ↦ (x, f x)) := measurable_id.prodMk hf
  rw [trueError, Measure.real, labeledLaw, Measure.map_apply hmeas (measurableSet_lossSet hh)]
  rfl

lemma measurable_of_mem_decisionStumps {h : ℝ → Bool} (hh : h ∈ decisionStumps) :
    Measurable h := by
  rcases hh with ⟨θ, rfl⟩ | ⟨θ, rfl⟩
  · refine measurable_to_bool ?_
    have : (fun x : ℝ ↦ decide (θ < x)) ⁻¹' {true} = Ioi θ := by ext x; simp
    rw [this]; exact measurableSet_Ioi
  · refine measurable_to_bool ?_
    have : (fun x : ℝ ↦ decide (x ≤ θ)) ⁻¹' {true} = Iic θ := by ext x; simp
    rw [this]; exact measurableSet_Iic

/-- Under realizability by a 3-piece classifier, some decision stump has true error at most
`1/3 + 1/24`. -/
lemma exists_good_stump (D : Measure ℝ) [IsProbabilityMeasure D] (f : ℝ → Bool)
    (hreal : Realizable threePieceClassifiers D f) :
    ∃ h₀ ∈ decisionStumps, trueError D f h₀ ≤ 1 / 3 + 1 / 24 := by
  obtain ⟨hs, ⟨θ₁, θ₂, b, hlt, rfl⟩, h0⟩ := hreal
  set hstar := threePiece θ₁ θ₂ b with hhstar
  have hnull : D {x | hstar x ≠ f x} = 0 := by
    rw [trueError, ENNReal.toReal_eq_zero_iff] at h0
    exact h0.resolve_right (measure_ne_top _ _)
  -- the error of `h` is at most the mass of any set containing the disagreement with `hstar`
  have herr : ∀ (h : ℝ → Bool) (U : Set ℝ), {x | h x ≠ hstar x} ⊆ U →
      trueError D f h ≤ D.real U := by
    intro h U hU
    have hsub : {x | h x ≠ f x} ⊆ U ∪ {x | hstar x ≠ f x} := by
      intro x hx
      by_cases hx' : hstar x = f x
      · left; apply hU; simp only [mem_setOf_eq] at hx ⊢; rw [hx']; exact hx
      · right; exact hx'
    calc trueError D f h = D.real {x | h x ≠ f x} := rfl
      _ ≤ D.real (U ∪ {x | hstar x ≠ f x}) := measureReal_mono hsub
      _ ≤ D.real U + D.real {x | hstar x ≠ f x} := measureReal_union_le _ _
      _ = D.real U := by
          rw [show D.real {x | hstar x ≠ f x} = 0 by simp [Measure.real, hnull], add_zero]
  -- the three regions have total mass at most `1`
  set p₁ := D.real (Iio θ₁)
  set p₂ := D.real (Icc θ₁ θ₂)
  set p₃ := D.real (Ioi θ₂)
  have hsum : p₁ + p₂ + p₃ ≤ 1 := by
    have d1 : Disjoint (Iio θ₁) (Icc θ₁ θ₂) :=
      Set.disjoint_left.2 fun x h1 h2 ↦ absurd h2.1 (not_le.2 h1)
    have d2 : Disjoint (Iio θ₁ ∪ Icc θ₁ θ₂) (Ioi θ₂) := by
      refine Set.disjoint_left.2 fun x h1 h2 ↦ ?_
      rcases h1 with h1 | h1
      · exact absurd (h1.trans hlt) (not_lt.2 (le_of_lt h2))
      · exact absurd h2 (not_lt.2 h1.2)
    have := measureReal_union d1 measurableSet_Icc (μ := D)
    have := measureReal_union d2 measurableSet_Ioi (μ := D)
    have : D.real ((Iio θ₁ ∪ Icc θ₁ θ₂) ∪ Ioi θ₂) ≤ 1 := by
      rw [← probReal_univ (μ := D)]; exact measureReal_mono (subset_univ _)
    linarith
  obtain ⟨θa, hθa, hma⟩ := exists_measureReal_Ioo_lt D θ₁ (ε := 1 / 24) (by norm_num)
  obtain ⟨θb, hθb, hmb⟩ := exists_measureReal_Ioi_lt D θ₂ (ε := 1 / 24) (by norm_num)
  have hu1 : ∀ U V : Set ℝ, D.real (U ∪ V) ≤ D.real U + D.real V :=
    fun U V ↦ measureReal_union_le _ _
  -- three candidate stumps, according to `b`
  obtain ⟨g₁, hg₁, e₁⟩ : ∃ g ∈ decisionStumps, trueError D f g ≤ p₁ := by
    cases b
    · refine ⟨fun x ↦ decide (x ≤ θ₂), Or.inr ⟨θ₂, rfl⟩, herr _ _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_Iio]
      by_contra hc
      push Not at hc
      by_cases h2 : θ₂ < x
      · simp [h2, not_le.2 h2, not_lt.2 hc] at hx
      · push Not at h2; simp [h2, not_lt.2 hc, not_lt.2 h2] at hx
    · refine ⟨fun x ↦ decide (θ₂ < x), Or.inl ⟨θ₂, rfl⟩, herr _ _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_Iio]
      by_contra hc
      push Not at hc
      by_cases h2 : θ₂ < x
      · simp [h2] at hx
      · push Not at h2; simp [not_lt.2 h2, not_lt.2 hc] at hx
  obtain ⟨g₂, hg₂, e₂⟩ : ∃ g ∈ decisionStumps, trueError D f g ≤ p₃ + 1 / 24 := by
    have hsub : ∀ g : ℝ → Bool, {x | g x ≠ hstar x} ⊆ Ioi θ₂ ∪ Ioo θa θ₁ →
        trueError D f g ≤ p₃ + 1 / 24 := by
      intro g hg
      have := herr g _ hg
      linarith [hu1 (Ioi θ₂) (Ioo θa θ₁)]
    cases b
    · refine ⟨fun x ↦ decide (θa < x), Or.inl ⟨θa, rfl⟩, hsub _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_union, mem_Ioi, mem_Ioo]
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      by_cases h1 : x < θ₁
      · have : x ≤ θa := by by_contra h; push Not at h; exact absurd (hc2 h) (not_le.2 h1)
        simp [h1, not_lt.2 this] at hx
      · push Not at h1; simp [not_lt.2 h1, not_lt.2 hc1, hθa.trans_le h1] at hx
    · refine ⟨fun x ↦ decide (x ≤ θa), Or.inr ⟨θa, rfl⟩, hsub _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_union, mem_Ioi, mem_Ioo]
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      by_cases h1 : x < θ₁
      · have : x ≤ θa := by by_contra h; push Not at h; exact absurd (hc2 h) (not_le.2 h1)
        simp [h1, this] at hx
      · push Not at h1
        simp [not_lt.2 h1, not_lt.2 hc1, not_le.2 (hθa.trans_le h1)] at hx
  obtain ⟨g₃, hg₃, e₃⟩ : ∃ g ∈ decisionStumps, trueError D f g ≤ p₂ + 1 / 24 := by
    have hsub : ∀ g : ℝ → Bool, {x | g x ≠ hstar x} ⊆ Icc θ₁ θ₂ ∪ Ioi θb →
        trueError D f g ≤ p₂ + 1 / 24 := by
      intro g hg
      have := herr g _ hg
      linarith [hu1 (Icc θ₁ θ₂) (Ioi θb)]
    cases b
    · refine ⟨fun x ↦ decide (θb < x), Or.inl ⟨θb, rfl⟩, hsub _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_union, mem_Icc, mem_Ioi]
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      by_cases h1 : x < θ₁
      · have : ¬ θb < x := fun h ↦ absurd (h1.trans (hlt.trans_le hθb)) (not_lt.2 h.le)
        simp [h1, this] at hx
      · push Not at h1
        have h2 : θ₂ < x := by by_contra h; push Not at h; exact absurd (hc1 h1) (not_lt.2 h)
        simp [h2, not_lt.2 hc2] at hx
    · refine ⟨fun x ↦ decide (x ≤ θb), Or.inr ⟨θb, rfl⟩, hsub _ ?_⟩
      intro x hx
      simp only [mem_setOf_eq, hhstar, threePiece] at hx
      simp only [mem_union, mem_Icc, mem_Ioi]
      by_contra hc
      push Not at hc
      obtain ⟨hc1, hc2⟩ := hc
      by_cases h1 : x < θ₁
      · have : x ≤ θb := (h1.trans (hlt.trans_le hθb)).le
        simp [h1, this] at hx
      · push Not at h1
        have h2 : θ₂ < x := by by_contra h; push Not at h; exact absurd (hc1 h1) (not_lt.2 h)
        simp [h2, hc2] at hx
  -- one of the three has error at most `1/3 + 1/24`
  by_cases c1 : p₁ ≤ 1 / 3
  · exact ⟨g₁, hg₁, by linarith⟩
  by_cases c3 : p₃ ≤ 1 / 3
  · exact ⟨g₂, hg₂, by linarith⟩
  · exact ⟨g₃, hg₃, by linarith⟩

end StumpsWeak

/-- **Example 10.1** (pp. 132–133). Let `X = ℝ`, `H` the class of 3-piece classifiers and `B`
the class of decision stumps. Then `ERM_B` is a γ-weak learner for `H` with `γ = 1/12`: for
every distribution consistent with `H` some decision stump has error at most `1/3`, and since
`VCdim(B) = 2`, with enough examples the `ERM_B` rule returns, with probability at least
`1 − δ`, a hypothesis with error at most `1/3 + 1/12 = 1/2 − 1/12`. Stated for every ERM
learner over the stumps, with one sample-size function. -/
theorem stumps_weakly_learn_three_piece :
    ∃ mH : ℝ → ℕ, ∀ A : Learner (ℝ × Bool) (ℝ → Bool), IsERMLearner loss01 decisionStumps A →
      IsWeakLearnerWith threePieceClassifiers (1 / 12) A mH := by
  refine ⟨fun δ ↦ ⌈(966 * 14400 : ℝ) / δ⌉₊ + 1, fun A hA ↦ ?_⟩
  intro δ hδ0 hδ1 D hD f hf hreal m hm
  set η : ℝ := 1 / 240 with hη
  set P := labeledLaw D f with hP
  haveI : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk hf).aemeasurable
  obtain ⟨𝓕, hcard, hmeas, hunif⟩ := stump_uniform_bracket P (by rw [probReal_univ])
    (η := η) (by norm_num) 240 (by norm_num)
  obtain ⟨h₀, hh₀, herr₀⟩ := exists_good_stump D f hreal
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos _) hm
  have hmR : (966 * 14400 : ℝ) / δ ≤ m := by
    have h1 := Nat.le_ceil ((966 * 14400 : ℝ) / δ)
    have h2 : ((⌈(966 * 14400 : ℝ) / δ⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2
    linarith
  -- outside the union of the bad events, the ERM output has small error
  have hsub : {S : Fin m → ℝ × Bool | 1 / 2 - 1 / 12 < trueError D f (A m S)} ⊆
      ⋃ E ∈ 𝓕, {S | η ≤ |empFreq S E - P.real E|} := by
    intro S hS
    by_contra hnot
    simp only [mem_iUnion, not_exists, mem_setOf_eq, not_le] at hnot hS
    have hdev : ∀ E ∈ 𝓕, |(empMeasure S).real E - P.real E| ≤ η := fun E hE ↦ by
      rw [empMeasure_real S (hmeas E hE)]; exact (hnot E hE).le
    have hU := hunif (empMeasure S) inferInstance hdev
    have hERM := hA m S
    have e1 := abs_le.1 (hU (A m S) hERM.1)
    have e2 := abs_le.1 (hU h₀ hh₀)
    have hle := hERM.2 h₀ hh₀
    rw [empRisk_eq_empFreq, empRisk_eq_empFreq,
      ← empMeasure_real S (measurableSet_lossSet (measurable_of_mem_decisionStumps hERM.1)),
      ← empMeasure_real S (measurableSet_lossSet (measurable_of_mem_decisionStumps hh₀))] at hle
    rw [trueError_eq_labeledLaw D hf (measurable_of_mem_decisionStumps hERM.1)] at hS
    rw [trueError_eq_labeledLaw D hf (measurable_of_mem_decisionStumps hh₀)] at herr₀
    rw [← hP] at hS herr₀
    obtain ⟨e11, e12⟩ := e1
    obtain ⟨e21, e22⟩ := e2
    rw [hη] at e11 e12 e21 e22
    linarith
  calc iidLaw P m {S | 1 / 2 - 1 / 12 < trueError D f (A m S)}
      ≤ iidLaw P m (⋃ E ∈ 𝓕, {S | η ≤ |empFreq S E - P.real E|}) := measure_mono hsub
    _ ≤ ∑ E ∈ 𝓕, iidLaw P m {S | η ≤ |empFreq S E - P.real E|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _E ∈ 𝓕, ENNReal.ofReal (1 / (4 * m * η ^ 2)) :=
        Finset.sum_le_sum fun E hE ↦ iidLaw_empFreq_dev_le P (hmeas E hE) hmpos (by norm_num)
    _ = ENNReal.ofReal (𝓕.card * (1 / (4 * m * η ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have hc : (𝓕.card : ℝ) ≤ 966 := by exact_mod_cast hcard
        have hmR' : (0 : ℝ) < m := by exact_mod_cast hmpos
        rw [hη]
        have : (𝓕.card : ℝ) * (1 / (4 * m * (1 / 240) ^ 2)) = 𝓕.card * 14400 / m := by
          field_simp; ring
        rw [this, div_le_iff₀ hmR']
        rw [div_le_iff₀ hδ0] at hmR
        nlinarith

end UnderstandingML

open UnderstandingML in
theorem solution :
    ∃ mH : ℝ → ℕ, ∀ A : Learner (ℝ × Bool) (ℝ → Bool), IsERMLearner loss01 decisionStumps A →
      IsWeakLearnerWith threePieceClassifiers (1 / 12) A mH :=
  UnderstandingML.stumps_weakly_learn_three_piece
