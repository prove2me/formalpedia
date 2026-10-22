-- Prove2me | solution 1 for ReedGGN.SystemEq.system_equation_2_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:25:57.854029+00:00
-- url     : https://prove2.me/submissions/e0379288-2dba-4d37-abc2-3dbc1b6bdbfc

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_NonIdling

set_option autoImplicit false
open MeasureTheory ReedGGN.SystemEq

lemma rgg_key (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (a b : ℝ)
    (hab : a ≤ b) : G μ a - G μ b = (μ (Set.Ioc a b ∩ Set.Ici 0)).toReal := by
  have h1 : μ (Set.Ioi a) = μ (Set.Ioc a b) + μ (Set.Ioi b) := by
    rw [← measure_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Ioc_union_Ioi_eq_Ioi hab]
  have h2 : μ (Set.Ioc a b ∩ Set.Ici 0) = μ (Set.Ioc a b) := by
    have : Set.Ioc a b ∩ Set.Ici 0 = Set.Ioc a b \ Set.Iio 0 := by
      rw [Set.diff_eq, Set.compl_Iio]
    rw [this, measure_diff_null hμ]
  rw [h2]
  unfold G
  rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

lemma rgg_reverse (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    ∫ s in Set.Icc 0 t,
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), if t - s < P.wt i then (1 : ℝ) else 0) ∂μ =
      ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t) := by
  have hind : ∀ i, (fun s : ℝ => if t - s < P.wt i then (1 : ℝ) else 0) =
      (Set.Ioi (t - P.wt i)).indicator (fun _ => (1 : ℝ)) := by
    intro i; funext s
    by_cases h : t - s < P.wt i
    · have : s ∈ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi]; linarith
      simp [h, this]
    · have : s ∉ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi, not_lt]; linarith
      simp [h, this]
  have hint : ∀ i ∈ Finset.Icc 1 (P.Q₀ - P.N),
      Integrable (fun s : ℝ => if t - s < P.wt i then (1 : ℝ) else 0) (μ.restrict (Set.Icc 0 t)) := by
    intro i _
    rw [hind i]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hab : t - P.wt i ≤ t := by linarith [P.wt_nonneg i]
  rw [rgg_key μ hμ _ _ hab, hind i, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply measurableSet_Ioi]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc, Set.mem_Ici]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩

lemma rgg_mem_A (P : SamplePath) (u : ℝ) (i : ℕ) (hi : 1 ≤ i) : i ≤ P.A u ↔ P.τ i ≤ u := by
  have hA : P.A u = Set.ncard {j : ℕ | 1 ≤ j ∧ P.τ j ≤ u} := by
    unfold SamplePath.A
    rw [← Nat.card_coe_set_eq]; rfl
  have hfin := P.τ_finite u
  rw [hA]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hsub : {j : ℕ | 1 ≤ j ∧ P.τ j ≤ u} ⊆ Finset.Icc 1 (i - 1) := by
      intro j hj
      simp only [Set.mem_setOf_eq] at hj
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hj.1, ?_⟩
      by_contra hji
      push_neg at hji
      have : P.τ i ≤ P.τ j := P.τ_mono (by omega)
      linarith [hj.2]
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega
  · intro h
    have hsub : (Finset.Icc 1 i : Set ℕ) ⊆ {j : ℕ | 1 ≤ j ∧ P.τ j ≤ u} := by
      intro j hj
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj
      exact ⟨hj.1, (P.τ_mono hj.2).trans h⟩
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega

lemma rgg_tau_nonneg (P : SamplePath) (i : ℕ) : 0 ≤ P.τ i := by
  have := P.τ_mono (Nat.zero_le i)
  rw [P.τ_zero] at this; exact this

lemma rgg_sum_A (P : SamplePath) {u t : ℝ} (hut : u ≤ t) :
    ∑ i ∈ Finset.Icc 1 (P.A u), (if P.τ i ≤ u ∧ u < P.τ i + P.w i then (1 : ℝ) else 0) =
      ∑ i ∈ Finset.Icc 1 (P.A t), (if P.τ i ≤ u ∧ u < P.τ i + P.w i then (1 : ℝ) else 0) := by
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have h1 := (rgg_mem_A P u i hi.1).1 hi.2
    exact (rgg_mem_A P t i hi.1).2 (h1.trans hut)
  · intro i hi hni
    simp only [Finset.mem_Icc, not_and, not_le] at hi hni
    have : ¬ P.τ i ≤ u := fun h => by
      have := (rgg_mem_A P u i hi.1).2 h
      have := hni hi.1
      omega
    simp [this]

lemma rgg_second (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    ∫ s in Set.Icc 0 t,
        (∑ i ∈ Finset.Icc 1 (P.A t),
          if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0) ∂μ =
      ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) := by
  have hind : ∀ i, (fun s : ℝ => if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0) =
      (Set.Ioc (t - P.τ i - P.w i) (t - P.τ i)).indicator (fun _ => (1 : ℝ)) := by
    intro i; funext s
    by_cases h : P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i
    · have : s ∈ Set.Ioc (t - P.τ i - P.w i) (t - P.τ i) := by
        simp only [Set.mem_Ioc]; constructor <;> linarith [h.1, h.2]
      simp [h, this]
    · have : s ∉ Set.Ioc (t - P.τ i - P.w i) (t - P.τ i) := by
        simp only [Set.mem_Ioc, not_and, not_le]
        intro h1
        by_contra h2
        push_neg at h2
        exact h ⟨by linarith, by linarith⟩
      simp [h, this]
  have hint : ∀ i ∈ Finset.Icc 1 (P.A t),
      Integrable (fun s : ℝ => if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0)
        (μ.restrict (Set.Icc 0 t)) := by
    intro i _
    rw [hind i]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hab : t - P.τ i - P.w i ≤ t - P.τ i := by linarith [P.w_nonneg i]
  rw [rgg_key μ hμ _ _ hab, hind i, integral_indicator measurableSet_Ioc, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply measurableSet_Ioc]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc, Set.mem_Ici]
  have := rgg_tau_nonneg P i
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by linarith [h1.2]⟩

lemma rgg_prop (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (hP : NonIdling P) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Set.Icc 0 t, max ((Q P (t - s) : ℝ) - P.N) 0 ∂μ) =
      (∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i))) +
        ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t) := by
  have hcongr : ∫ s in Set.Icc 0 t, max ((Q P (t - s) : ℝ) - P.N) 0 ∂μ =
      ∫ s in Set.Icc 0 t,
        ((∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), if t - s < P.wt i then (1 : ℝ) else 0) +
         ∑ i ∈ Finset.Icc 1 (P.A t),
          if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [Set.mem_Icc] at hs
    have h0 : 0 ≤ t - s := by linarith [hs.2]
    show max ((Q P (t - s) : ℝ) - P.N) 0 = _
    rw [hP (t - s) h0, rgg_sum_A P (u := t - s) (t := t) (by linarith [hs.1])]
  rw [hcongr]
  have hi1 : Integrable (fun s : ℝ => ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N),
      if t - s < P.wt i then (1 : ℝ) else 0) (μ.restrict (Set.Icc 0 t)) := by
    refine integrable_finset_sum _ fun i _ => ?_
    have : (fun s : ℝ => if t - s < P.wt i then (1 : ℝ) else 0) =
        (Set.Ioi (t - P.wt i)).indicator (fun _ => (1 : ℝ)) := by
      funext s
      by_cases h : t - s < P.wt i
      · have : s ∈ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi]; linarith
        simp [h, this]
      · have : s ∉ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi, not_lt]; linarith
        simp [h, this]
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hi2 : Integrable (fun s : ℝ => ∑ i ∈ Finset.Icc 1 (P.A t),
      if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0) (μ.restrict (Set.Icc 0 t)) := by
    refine integrable_finset_sum _ fun i _ => ?_
    have : (fun s : ℝ => if P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i then (1 : ℝ) else 0) =
        (Set.Ioc (t - P.τ i - P.w i) (t - P.τ i)).indicator (fun _ => (1 : ℝ)) := by
      funext s
      by_cases h : P.τ i ≤ t - s ∧ t - s < P.τ i + P.w i
      · have : s ∈ Set.Ioc (t - P.τ i - P.w i) (t - P.τ i) := by
          simp only [Set.mem_Ioc]; constructor <;> linarith [h.1, h.2]
        simp [h, this]
      · have : s ∉ Set.Ioc (t - P.τ i - P.w i) (t - P.τ i) := by
          simp only [Set.mem_Ioc, not_and, not_le]
          intro h1
          by_contra h2
          push_neg at h2
          exact h ⟨by linarith, by linarith⟩
        simp [h, this]
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
  rw [integral_add hi1 hi2, rgg_reverse μ hμ P t ht, rgg_second μ hμ P t ht]
  ring

theorem solution (μ μ₀ : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ₀] (hμ : μ (Set.Iio 0) = 0) (hμ₀ : μ₀ (Set.Iio 0) = 0)
    (P : SamplePath) (hP : NonIdling P) (t : ℝ) (ht : 0 ≤ t) :
    (Q P t : ℝ) =
      I μ μ₀ P t + W0 μ₀ P t + M2 μ P t + AG μ P t +
        ∫ s in Set.Icc 0 t, max ((Q P (t - s) : ℝ) - P.N) 0 ∂μ := by
  have h27 : (Q P t : ℝ) =
      I μ μ₀ P t + W0 μ₀ P t + M2 μ P t + AG μ P t +
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t)) +
        ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) := by
    simp only [Q, I, W0, M2, AG, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, Finset.card_filter]
    push_cast
    simp
    ring
  rw [h27, rgg_prop μ hμ P hP t ht]; ring
