-- Prove2me | solution 1 for RobustSPA.FixedReserve.regret_spa_fixed_aff_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:03:40.011421+00:00
-- url     : https://prove2.me/submissions/d1e9117c-2486-4ba6-869f-7f334f8ce4c5

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting
import Theorems.Thm_RobustSPA_Affiliated_lemma_1
import Theorems.Thm_RobustSPA_Affiliated_second_order_stat_identity
import Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff
import Theorems.Thm_RobustSPA_FixedReserve_sup_over_c
import Theorems.Thm_RobustSPA_FixedReserve_sup_over_c_one
import Theorems.Thm_RobustSPA_FixedReserve_optimal_reserve

open MeasureTheory Set

namespace FRP
open scoped Classical
open RobustSPA.FixedReserve

variable {n : ℕ}

lemma isWinner_unique {v : Fin n → ℝ} {i j : Fin n} (hi : isWinner v i) (hj : isWinner v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2 i h; have := hi.1 j; linarith
  · exact h
  · have := hi.2 j h; have := hj.1 i; linarith

/-- the highest competing valuation -/
noncomputable def cmax (v : Fin n → ℝ) (i : Fin n) : ℝ := ⨆ j : {j : Fin n // j ≠ i}, v j

lemma le_cmax (v : Fin n → ℝ) (i j : Fin n) (hj : j ≠ i) : v j ≤ cmax v i :=
  le_ciSup (f := fun j : {j : Fin n // j ≠ i} => v j) (Finite.bddAbove_range _) ⟨j, hj⟩

lemma le_second (v : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) : min (v a) (v b) ≤ second v :=
  le_ciSup (f := fun q : {q : Fin n × Fin n // q.1 ≠ q.2} => min (v q.1.1) (v q.1.2))
    (Finite.bddAbove_range _) ⟨(a, b), hab⟩

lemma second_eq_cmax {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : second v = cmax v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · obtain ⟨⟨j0, hj0⟩⟩ := hne
    haveI : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2} := ⟨⟨(i, j0), fun h => hj0 h.symm⟩⟩
    haveI : Nonempty {j : Fin n // j ≠ i} := ⟨⟨j0, hj0⟩⟩
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha
        exact (min_le_right _ _).trans (le_cmax v a b (Ne.symm hab))
      · exact (min_le_left _ _).trans (le_cmax v i a ha)
    · apply ciSup_le
      rintro ⟨j, hj⟩
      have h1 : min (v i) (v j) = v j := min_eq_right (hw.1 j)
      calc v j = min (v i) (v j) := h1.symm
        _ ≤ second v := le_second v i j (fun h => hj h.symm)
  · haveI h1 : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    haveI h2 : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := by
      constructor
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha; exact h1.false ⟨b, Ne.symm hab⟩
      · exact h1.false ⟨a, ha⟩
    unfold second cmax
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]

lemma cmax_le_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) (h0 : 0 ≤ v i) :
    cmax v i ≤ v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · exact ciSup_le (fun j => hw.1 j)
  · haveI : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    unfold cmax; rw [Real.iSup_of_isEmpty]; exact h0

lemma second_nonneg {v : Fin n → ℝ} (hv : v ∈ cube n) : 0 ≤ second v := by
  by_cases hne : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2}
  · obtain ⟨⟨⟨a, b⟩, hab⟩⟩ := hne
    refine le_trans ?_ (le_second v a b hab)
    exact le_min (hv a (Set.mem_univ _)).1 (hv b (Set.mem_univ _)).1
  · haveI : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := not_nonempty_iff.mp hne
    unfold second; rw [Real.iSup_of_isEmpty]

lemma second_le_one {v : Fin n → ℝ} (hv : v ∈ cube n) : second v ≤ 1 := by
  unfold second
  apply Real.iSup_le _ zero_le_one
  rintro ⟨⟨a, b⟩, _⟩
  exact (min_le_left _ _).trans (hv a (Set.mem_univ _)).2

lemma meas_second : Measurable (fun v : Fin n → ℝ => second v) := by
  unfold second
  exact Measurable.iSup (fun q => (measurable_pi_apply _).min (measurable_pi_apply _))

lemma exists_winner (hn : 0 < n) (v : Fin n → ℝ) : ∃ i, isWinner v i := by
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let S := Finset.univ.filter (fun i => ∀ j, v j ≤ v i)
  have hS : S.Nonempty := ⟨i1, by simp [S]; exact fun j => hi1 j (Finset.mem_univ _)⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have := S.min'_mem hS
    simp only [S, Finset.mem_filter] at this
    exact this.2
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hmem := S.min'_mem hS
    simp only [S, Finset.mem_filter] at hmem
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k; exact (hmem.2 k).trans hcon
    exact absurd (S.min'_le j hjS) (not_le.2 hj)

lemma top_eq_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : top v = v i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  exact le_antisymm (ciSup_le hw.1) (le_ciSup (Finite.bddAbove_range v) i)


lemma sum_p_SPA (ρ : Measure ℝ) {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) :
    ∑ j, (SPA (n := n) ρ).p j v =
      ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ := by
  rw [Finset.sum_eq_single i (fun j _ hj => by
        show (if isWinner v j then _ else _) = _
        rw [if_neg (fun hw' => hj (isWinner_unique hw' hw))])
        (fun h => absurd (Finset.mem_univ i) h)]
  show (if isWinner v i then _ else _) = _
  rw [if_pos hw]

lemma top_nonneg {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : 0 ≤ top v := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw]; exact (hv i (Set.mem_univ _)).1

lemma top_le_one {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : top v ≤ 1 := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw]; exact (hv i (Set.mem_univ _)).2

lemma second_le_top {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : second v ≤ top v := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw, second_eq_cmax hw]
  exact cmax_le_of_winner hw (hv i (Set.mem_univ _)).1

lemma meas_top : Measurable (fun v : Fin n → ℝ => top v) := by
  unfold top
  exact Measurable.iSup (fun i => measurable_pi_apply i)


/-- CDF of the highest valuation. -/
noncomputable def F1 (μ : Measure (Fin n → ℝ)) (t : ℝ) : ℝ := (μ {u | top u ≤ t}).toReal
/-- CDF of the second-highest valuation. -/
noncomputable def F2 (μ : Measure (Fin n → ℝ)) (t : ℝ) : ℝ := (μ {u | second u ≤ t}).toReal

lemma F1_mono (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F1 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun u hu => le_trans hu hab

lemma F2_mono (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F2 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun u hu => le_trans hu hab

lemma toReal_le_one' {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := μ) (s := s))

/-- Pointwise regret of `SPA(r)`. -/
lemma pointwise_fixed (hn : 0 < n) (r : ℝ) (v : Fin n → ℝ) :
    top v - ∑ i, (SPA (n := n) (Measure.dirac r)).p i v =
      if top v < r then top v else top v - max (second v) r := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [sum_p_SPA _ hw, integral_dirac, ← top_eq_of_winner hw]
  by_cases h : top v < r
  · rw [if_pos h, Set.indicator_of_notMem (show r ∉ Set.Iic (top v) from fun h' => by
      simp only [Set.mem_Iic] at h'; linarith)]
    ring
  · rw [if_neg h, Set.indicator_of_mem (show r ∈ Set.Iic (top v) from not_lt.mp h)]

lemma int_ind (S : Set ℝ) (hS : MeasurableSet S) :
    ∫ t in Set.Icc (0 : ℝ) 1, S.indicator (fun _ => (1 : ℝ)) t = volume.real (S ∩ Set.Icc 0 1) := by
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_one, measureReal_restrict_apply hS]

lemma vol_Ico (a b : ℝ) (h : a ≤ b) : volume.real (Set.Ico a b) = b - a := by
  rw [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- The exact regret of `SPA(r)` for a law on the cube. -/
theorem regret_fixed_formula (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fall n) :
    regret (SPA (Measure.dirac r)) μ =
      r * (μ {v | top v < r}).toReal - (∫ t in (0 : ℝ)..r, F1 μ t) +
        ∫ t in r..1, (F2 μ t - F1 μ t) := by
  haveI := hμ.1
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]; simpa [Set.compl_def] using hμ.2
  set A : (Fin n → ℝ) → Set ℝ := fun v => {t | t < top v ∧ top v < r} with hA
  set B : (Fin n → ℝ) → Set ℝ := fun v => {t | r ≤ t ∧ second v ≤ t ∧ t < top v} with hB
  have mA : ∀ v, MeasurableSet (A v) := fun v =>
    (measurableSet_lt measurable_id measurable_const).inter
      (MeasurableSet.const _)
  have mB : ∀ v, MeasurableSet (B v) := fun v =>
    (measurableSet_le measurable_const measurable_id).inter
      ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const))
  set k : (Fin n → ℝ) → ℝ → ℝ := fun v t =>
    (A v).indicator (fun _ => (1 : ℝ)) t + (B v).indicator (fun _ => (1 : ℝ)) t with hk
  have hb1 : ∀ (S : Set ℝ) t, |S.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := fun S t => by
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]; norm_num
    · rw [Set.indicator_of_notMem ht]; norm_num
  have intOn : ∀ (S : Set ℝ), MeasurableSet S →
      IntegrableOn (S.indicator (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := fun S hS =>
    IntegrableOn.indicator (continuous_const.integrableOn_Icc) hS
  -- pointwise identity
  have hpt : ∀ v ∈ cube n, top v - ∑ i, (SPA (n := n) (Measure.dirac r)).p i v =
      ∫ t in Set.Icc (0 : ℝ) 1, k v t := by
    intro v hv
    have h0 := top_nonneg hn hv
    have h1 := top_le_one hn hv
    have hs0 := second_nonneg hv
    have hst := second_le_top hn hv
    rw [pointwise_fixed hn r v]
    simp only [hk]
    rw [integral_add (intOn _ (mA v)) (intOn _ (mB v)), int_ind _ (mA v), int_ind _ (mB v)]
    by_cases hx : top v < r
    · rw [if_pos hx]
      have e1 : A v ∩ Set.Icc 0 1 = Set.Ico 0 (top v) := by
        ext t; simp only [hA, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨⟨h1, _⟩, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1'⟩; exact ⟨⟨h1', hx⟩, h2, by linarith⟩
      have e2 : B v ∩ Set.Icc 0 1 = ∅ := by
        ext t; simp only [hB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨h1, _, h3⟩, _⟩; linarith
      rw [e1, e2, vol_Ico _ _ h0, measureReal_empty]; ring
    · rw [if_neg hx]
      push_neg at hx
      have e1 : A v ∩ Set.Icc 0 1 = ∅ := by
        ext t; simp only [hA, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨⟨_, h2⟩, _⟩; linarith
      have e2 : B v ∩ Set.Icc 0 1 = Set.Ico (max (second v) r) (top v) := by
        ext t; simp only [hB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ico,
          max_le_iff]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, _⟩; exact ⟨⟨h2, h1⟩, h3⟩
        · rintro ⟨⟨h2, h1⟩, h3⟩; exact ⟨⟨h1, h2, h3⟩, by linarith, by linarith⟩
      rw [e1, e2, vol_Ico _ _ (max_le hst hx), measureReal_empty]; ring
  -- Fubini
  have hmeas_k : Measurable (Function.uncurry k) := by
    have m1 : Measurable (fun p : (Fin n → ℝ) × ℝ => (A p.1).indicator (fun _ => (1 : ℝ)) p.2) := by
      have : (fun p : (Fin n → ℝ) × ℝ => (A p.1).indicator (fun _ => (1 : ℝ)) p.2) =
          {p : (Fin n → ℝ) × ℝ | p.2 < top p.1 ∧ top p.1 < r}.indicator (fun _ => 1) := by
        ext p; simp [hA, Set.indicator_apply]
      rw [this]
      exact measurable_const.indicator
        ((measurableSet_lt measurable_snd (meas_top.comp measurable_fst)).inter
          (measurableSet_lt (meas_top.comp measurable_fst) measurable_const))
    have m2 : Measurable (fun p : (Fin n → ℝ) × ℝ => (B p.1).indicator (fun _ => (1 : ℝ)) p.2) := by
      have : (fun p : (Fin n → ℝ) × ℝ => (B p.1).indicator (fun _ => (1 : ℝ)) p.2) =
          {p : (Fin n → ℝ) × ℝ | r ≤ p.2 ∧ second p.1 ≤ p.2 ∧ p.2 < top p.1}.indicator
            (fun _ => 1) := by
        ext p; simp [hB, Set.indicator_apply]
      rw [this]
      exact measurable_const.indicator
        ((measurableSet_le measurable_const measurable_snd).inter
          ((measurableSet_le (meas_second.comp measurable_fst) measurable_snd).inter
            (measurableSet_lt measurable_snd (meas_top.comp measurable_fst))))
    exact m1.add m2
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [isFiniteMeasure_restrict]; simp
  have hint_k : Integrable (Function.uncurry k) (μ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    refine Integrable.of_bound hmeas_k.aestronglyMeasurable 2 (Filter.Eventually.of_forall ?_)
    rintro ⟨v, t⟩
    simp only [Function.uncurry_apply_pair, hk, Real.norm_eq_abs]
    calc _ ≤ |(A v).indicator (fun _ => (1 : ℝ)) t| + |(B v).indicator (fun _ => (1 : ℝ)) t| :=
          abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (hb1 _ _) (hb1 _ _)
      _ = 2 := by norm_num
  -- inner integrals
  set P : ℝ := (μ {v | top v < r}).toReal with hP
  set h : ℝ → ℝ := fun t => (if t < r then P - F1 μ t else 0) +
    (if r ≤ t then F2 μ t - F1 μ t else 0) with hh
  have mT : ∀ t, MeasurableSet {v : Fin n → ℝ | top v ≤ t} := fun t =>
    measurableSet_le meas_top measurable_const
  have mS : ∀ t, MeasurableSet {v : Fin n → ℝ | second v ≤ t} := fun t =>
    measurableSet_le meas_second measurable_const
  have mTr : MeasurableSet {v : Fin n → ℝ | top v < r} := measurableSet_lt meas_top measurable_const
  have hinner : ∀ t, ∫ v, k v t ∂μ = h t := by
    intro t
    have e1 : (fun v => (A v).indicator (fun _ => (1 : ℝ)) t) =
        {v : Fin n → ℝ | t < top v ∧ top v < r}.indicator (fun _ => 1) := by
      ext v; simp [hA, Set.indicator_apply]
    have e2 : (fun v => (B v).indicator (fun _ => (1 : ℝ)) t) =
        {v : Fin n → ℝ | r ≤ t ∧ second v ≤ t ∧ t < top v}.indicator (fun _ => 1) := by
      ext v; simp [hB, Set.indicator_apply]
    have mA' : MeasurableSet {v : Fin n → ℝ | t < top v ∧ top v < r} :=
      (measurableSet_lt measurable_const meas_top).inter mTr
    have mB' : MeasurableSet {v : Fin n → ℝ | r ≤ t ∧ second v ≤ t ∧ t < top v} :=
      (MeasurableSet.const _).inter ((mS t).inter (measurableSet_lt measurable_const meas_top))
    have e3 : (fun v => k v t) = fun v =>
        {v : Fin n → ℝ | t < top v ∧ top v < r}.indicator (fun _ => (1 : ℝ)) v +
        {v : Fin n → ℝ | r ≤ t ∧ second v ≤ t ∧ t < top v}.indicator (fun _ => (1 : ℝ)) v := by
      ext v; simp only [hk]; rw [← congrFun e1 v, ← congrFun e2 v]
    rw [e3, integral_add ((integrable_const _).indicator mA') ((integrable_const _).indicator mB'),
      integral_indicator_const _ mA', integral_indicator_const _ mB', smul_eq_mul, smul_eq_mul,
      mul_one, mul_one]
    simp only [hh]
    congr 1
    · by_cases ht : t < r
      · rw [if_pos ht]
        have : {v : Fin n → ℝ | t < top v ∧ top v < r} =
            {v | top v < r} \ {v | top v ≤ t} := by
          ext v; simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]; tauto
        rw [this, measureReal_sdiff (s₁ := {v : Fin n → ℝ | top v < r}) (s₂ := {v | top v ≤ t})
          (fun v hv => lt_of_le_of_lt (show top v ≤ t from hv) ht) (mT t) (measure_ne_top _ _)]
        rfl
      · rw [if_neg ht]
        have : {v : Fin n → ℝ | t < top v ∧ top v < r} = ∅ := by
          ext v; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; exact ht (lt_trans h1 h2)
        rw [this, measureReal_empty]
    · by_cases ht : r ≤ t
      · rw [if_pos ht]
        have : {v : Fin n → ℝ | r ≤ t ∧ second v ≤ t ∧ t < top v} =
            {v | second v ≤ t} \ {v | top v ≤ t} := by
          ext v; simp only [Set.mem_setOf_eq, Set.mem_diff, not_le]; tauto
        rw [this]
        have hBA : μ ({v : Fin n → ℝ | top v ≤ t} \ {v | second v ≤ t}) = 0 := by
          apply measure_mono_null _ hμ.2
          intro v hv hvc
          exact hv.2 (le_trans (second_le_top hn hvc) hv.1)
        have hsplitA := measure_diff_add_inter (μ := μ) {v : Fin n → ℝ | second v ≤ t} (mT t)
        have hsplitB := measure_inter_add_diff (μ := μ) {v : Fin n → ℝ | top v ≤ t} (mS t)
        rw [hBA, add_zero, Set.inter_comm] at hsplitB
        rw [hsplitB] at hsplitA
        have := congrArg ENNReal.toReal hsplitA
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
        simp only [Measure.real, F1, F2]
        linarith
      · rw [if_neg ht]
        have : {v : Fin n → ℝ | r ≤ t ∧ second v ≤ t ∧ t < top v} = ∅ := by
          ext v; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro h1; exact absurd h1 ht
        rw [this, measureReal_empty]
  -- assemble
  have hreg : regret (SPA (Measure.dirac r)) μ = ∫ t in Set.Icc (0 : ℝ) 1, h t := by
    unfold regret
    rw [integral_congr_ae (hae.mono fun v hv => hpt v hv), integral_integral_swap hint_k]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => hinner t
  have hint_h : IntegrableOn h (Set.Icc (0 : ℝ) 1) := by
    have := hint_k.integral_prod_right
    rwa [show (fun t => ∫ v, Function.uncurry k (v, t) ∂μ) = h from funext hinner] at this
  have hsplit : Set.Icc (0 : ℝ) 1 = Set.Ico 0 r ∪ Set.Icc r 1 := by
    ext t; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ico]
    constructor
    · rintro ⟨h0, h1⟩
      by_cases ht : t < r
      · left; exact ⟨h0, ht⟩
      · right; exact ⟨not_lt.mp ht, h1⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact ⟨h0, by linarith [hr.2]⟩
      · exact ⟨by linarith [hr.1], h1⟩
  have hdisj : Disjoint (Set.Ico (0 : ℝ) r) (Set.Icc r 1) := by
    rw [Set.disjoint_left]; rintro t ⟨_, h1⟩ ⟨h2, _⟩; linarith
  rw [hreg, hsplit, setIntegral_union hdisj measurableSet_Icc
    (hint_h.mono_set (by rw [hsplit]; exact Set.subset_union_left))
    (hint_h.mono_set (by rw [hsplit]; exact Set.subset_union_right))]
  have hF1i : IntervalIntegrable (F1 μ) volume 0 r := (F1_mono μ).intervalIntegrable
  have p1 : ∫ t in Set.Ico (0 : ℝ) r, h t = r * P - ∫ t in (0 : ℝ)..r, F1 μ t := by
    rw [setIntegral_congr_fun measurableSet_Ico (g := fun t => P - F1 μ t) (fun t ht => by
      simp only [hh, if_pos ht.2, if_neg (not_le.mpr ht.2)]; ring),
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1,
      intervalIntegral.integral_sub intervalIntegrable_const hF1i]
    simp
  have p2 : ∫ t in Set.Icc r 1, h t = ∫ t in r..1, (F2 μ t - F1 μ t) := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun t => F2 μ t - F1 μ t) (fun t ht => by
      simp only [hh, if_neg (not_lt.mpr ht.1), if_pos ht.1]; ring),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.2]
  rw [p1, p2]

/-- `φ(z) = n z^{n-1} - n z^n`. -/
noncomputable def phi (n : ℕ) (z : ℝ) : ℝ := (n : ℝ) * z ^ (n - 1) - (n : ℝ) * z ^ n

/-- `g(c) = r cⁿ + (1-r) φ(c)`. -/
noncomputable def gfun (n : ℕ) (r c : ℝ) : ℝ := r * c ^ n + (1 - r) * phi n c

lemma phi_cont (n : ℕ) : Continuous (phi n) := by unfold phi; fun_prop

lemma phi_abs (n : ℕ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) : |phi n z| ≤ 2 * n := by
  unfold phi
  have h1 : z ^ (n - 1) ≤ 1 := pow_le_one₀ hz.1 hz.2
  have h2 : z ^ n ≤ 1 := pow_le_one₀ hz.1 hz.2
  have h3 : 0 ≤ z ^ (n - 1) := pow_nonneg hz.1 _
  have h4 : 0 ≤ z ^ n := pow_nonneg hz.1 _
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [abs_le]; constructor <;> nlinarith

/-- `φ(z) ≤ φ(max(c, (n-1)/n))` for `0 ≤ c ≤ z ≤ 1`. -/
lemma phi_le_max (hn : 0 < n) {c z : ℝ} (hc : 0 ≤ c) (hcz : c ≤ z) (hz : z ≤ 1) :
    phi n z ≤ phi n (max c (((n : ℝ) - 1) / n)) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp only [phi, Nat.cast_one, sub_self, zero_div, max_eq_left hc, pow_one]
    norm_num
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  set N : ℝ := ((k + 2 : ℕ) : ℝ) with hN
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hNpos : 0 < N := by linarith
  have hk1 : k + 2 - 1 = k + 1 := by omega
  have hderiv : ∀ x, HasDerivAt (phi (k + 2)) (N * x ^ k * ((N - 1) - N * x)) x := by
    intro x
    have h1 := hasDerivAt_pow (k + 1) x
    have h2 := hasDerivAt_pow (k + 2) x
    have := (h1.const_mul N).sub (h2.const_mul N)
    unfold phi
    rw [hk1]
    refine this.congr_deriv ?_
    rw [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
    rw [hN]; push_cast; ring
  set m : ℝ := (N - 1) / N with hm
  have hm0 : 0 ≤ m := div_nonneg (by linarith) hNpos.le
  have hm1 : m ≤ 1 := by rw [hm, div_le_one hNpos]; linarith
  have hNm : N * m = N - 1 := by rw [hm]; field_simp
  have mono : MonotoneOn (phi (k + 2)) (Set.Icc 0 m) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (phi_cont _).continuousOn
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have : N * x ≤ N * m := mul_le_mul_of_nonneg_left hx.2.le hNpos.le
    exact mul_nonneg (mul_nonneg hNpos.le (pow_nonneg hx.1.le _)) (by linarith)
  have anti : AntitoneOn (phi (k + 2)) (Set.Icc m 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (phi_cont _).continuousOn
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have : N * m ≤ N * x := mul_le_mul_of_nonneg_left hx.1.le hNpos.le
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hNpos.le (pow_nonneg (hm0.trans hx.1.le) _))
      (by linarith)
  rcases le_total z m with hzm | hzm
  · rw [max_eq_right (hcz.trans hzm)]
    exact mono ⟨hc.trans hcz, hzm⟩ ⟨hm0, le_rfl⟩ hzm
  · exact anti ⟨le_max_right _ _, max_le (hcz.trans hz) hm1⟩ ⟨hzm, hz⟩ (max_le hcz hzm)

/-- The facts about `W = wcFixed n r` as the maximum of `g` on `[(n-1)/n, 1]`. -/
lemma W_facts (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (∀ c ∈ Set.Icc (((n : ℝ) - 1) / n) 1, gfun n r c ≤ wcFixed n r) ∧
      ∃ c ∈ Set.Icc (((n : ℝ) - 1) / n) 1, gfun n r c = wcFixed n r := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have H := sup_over_c_one r hr
    have hg : ∀ c, gfun 1 r c = r * c + (1 - r) * (1 - c) := fun c => by
      simp [gfun, phi]
    simp only [wcFixed, if_true, Nat.cast_one, sub_self, zero_div]
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [hg]; exact H.2 ⟨c, hc, rfl⟩
    · obtain ⟨c, hc, hc'⟩ := H.1
      exact ⟨c, hc, by rw [hg]; exact hc'⟩
  · have H := sup_over_c n h2 r hr
    simp only at H
    have hne : n ≠ 1 := by omega
    have hg : ∀ c, gfun n r c =
        r * c ^ n + (1 - r) * ((n : ℝ) * c ^ (n - 1) - (n : ℝ) * c ^ n) := fun c => rfl
    simp only [wcFixed, if_neg hne]
    by_cases hrh : r ≤ 1 / 2
    · rw [if_pos hrh]
      obtain ⟨_, _, hG⟩ := H.1 hrh
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [hg]; exact hG.2 ⟨c, hc, rfl⟩
      · obtain ⟨c, hc, hc'⟩ := hG.1
        exact ⟨c, hc, by rw [hg]; exact hc'⟩
    · rw [if_neg hrh]
      push_neg at hrh
      obtain ⟨_, hG⟩ := H.2 hrh.le
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [hg]; exact hG.2 ⟨c, hc, rfl⟩
      · obtain ⟨c, hc, hc'⟩ := hG.1
        exact ⟨c, hc, by rw [hg]; exact hc'⟩

lemma bound_c (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    r * c ^ n + (1 - r) * phi n (max c (((n : ℝ) - 1) / n)) ≤ wcFixed n r := by
  have hm1 : ((n : ℝ) - 1) / n ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]; linarith
  have hmem : max c (((n : ℝ) - 1) / n) ∈ Set.Icc (((n : ℝ) - 1) / n) 1 :=
    ⟨le_max_right _ _, max_le hc.2 hm1⟩
  have h := (W_facts hn r hr).1 _ hmem
  unfold gfun at h
  have : r * c ^ n ≤ r * (max c (((n : ℝ) - 1) / n)) ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.1 (le_max_left _ _) n) hr.1
  linarith

/-- The generic upper bound. -/
theorem gen_bound (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fall n) {β : Type*} [MeasurableSpace β]
    (M : Measure β) [IsProbabilityMeasure M] (Z : β → ℝ → ℝ)
    (hZm : ∀ t, Measurable fun b => Z b t)
    (hZ01 : ∀ᵐ b ∂M, ∀ t, Z b t ∈ Set.Icc (0 : ℝ) 1)
    (hZmono : ∀ᵐ b ∂M, ∀ t ∈ Set.Icc r 1, Z b r ≤ Z b t)
    (hF1 : F1 μ r ≤ ∫ b, Z b r ^ n ∂M)
    (hF2 : ∀ t ∈ Set.Icc r 1, F2 μ t - F1 μ t ≤ ∫ b, phi n (Z b t) ∂M) :
    regret (SPA (Measure.dirac r)) μ ≤ wcFixed n r := by
  haveI := hμ.1
  rw [regret_fixed_formula hn r hr μ hμ]
  have hP : (μ {v | top v < r}).toReal ≤ F1 μ r :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun v (hv : top v < r) => (le_of_lt hv : top v ≤ r))
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..r, F1 μ t :=
    intervalIntegral.integral_nonneg hr.1 fun t _ => ENNReal.toReal_nonneg
  set m : ℝ := ((n : ℝ) - 1) / n
  set C : ℝ := ∫ b, phi n (max (Z b r) m) ∂M with hC
  have intb : ∀ f : β → ℝ, Measurable f → (∀ᵐ b ∂M, |f b| ≤ 2 * n) → Integrable f M :=
    fun f hf hb => Integrable.of_bound hf.aestronglyMeasurable (2 * n)
      (hb.mono fun b h => by rw [Real.norm_eq_abs]; exact h)
  have hmax01 : ∀ᵐ b ∂M, max (Z b r) m ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hZ01] with b hb
    have hm1 : m ≤ 1 := by
      show ((n : ℝ) - 1) / n ≤ 1
      rw [div_le_one (by exact_mod_cast hn)]; linarith
    exact ⟨le_max_of_le_left (hb r).1, max_le (hb r).2 hm1⟩
  have iC : Integrable (fun b => phi n (max (Z b r) m)) M :=
    intb _ ((phi_cont n).measurable.comp ((hZm r).max measurable_const))
      (hmax01.mono fun b h => phi_abs n h)
  have h2 : ∫ t in r..1, (F2 μ t - F1 μ t) ≤ (1 - r) * C := by
    have : ∫ t in r..1, (F2 μ t - F1 μ t) ≤ ∫ t in r..1, C := by
      apply intervalIntegral.integral_mono_on hr.2
        ((F2_mono μ).intervalIntegrable.sub (F1_mono μ).intervalIntegrable) intervalIntegrable_const
      intro t ht
      refine (hF2 t ht).trans (integral_mono_ae ?_ iC ?_)
      · exact intb _ ((phi_cont n).measurable.comp (hZm t)) (hZ01.mono fun b h => phi_abs n (h t))
      · filter_upwards [hZ01, hZmono] with b hb hbm
        exact phi_le_max hn (hb r).1 (hbm t ht) (hb t).2
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have iZ : Integrable (fun b => Z b r ^ n) M := by
    refine Integrable.of_bound ((hZm r).pow_const n).aestronglyMeasurable 1 ?_
    filter_upwards [hZ01] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb r).1 _)]
    exact pow_le_one₀ (hb r).1 (hb r).2
  have hfin : r * (∫ b, Z b r ^ n ∂M) + (1 - r) * C ≤ wcFixed n r := by
    rw [hC, ← integral_const_mul, ← integral_const_mul, ← integral_add (iZ.const_mul r)
      (iC.const_mul (1 - r))]
    calc ∫ b, (r * Z b r ^ n + (1 - r) * phi n (max (Z b r) m)) ∂M
        ≤ ∫ _b, wcFixed n r ∂M := by
          apply integral_mono_ae ((iZ.const_mul r).add (iC.const_mul (1 - r)))
            (integrable_const _)
          filter_upwards [hZ01] with b hb
          exact bound_c hn r hr (hb r)
      _ = wcFixed n r := by simp
  have hr1 : 0 ≤ 1 - r := by linarith [hr.2]
  nlinarith [mul_le_mul_of_nonneg_left hP hr.1, mul_le_mul_of_nonneg_left hF1 hr.1]

lemma F1_nonneg (μ : Measure (Fin n → ℝ)) (t : ℝ) : 0 ≤ F1 μ t := ENNReal.toReal_nonneg

/-- For one buyer the second-highest valuation is `0`, so `F2 = 1` on `[0, ∞)`. -/
lemma F2_one (μ : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 ≤ t) :
    F2 μ t = 1 := by
  have hs : ∀ u : Fin 1 → ℝ, second u = 0 := by
    intro u
    haveI : IsEmpty {q : Fin 1 × Fin 1 // q.1 ≠ q.2} :=
      ⟨fun q => q.2 (Subsingleton.elim _ _)⟩
    unfold second; exact Real.iSup_of_isEmpty _
  have : {u : Fin 1 → ℝ | second u ≤ t} = Set.univ := by
    ext u; simp [hs u, ht]
  simp [F2, this]

/-- Upper bound for one buyer, any law on `[0,1]`. -/
theorem ub_one (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (μ : Measure (Fin 1 → ℝ)) (hμ : μ ∈ Fall 1) :
    regret (SPA (Measure.dirac r)) μ ≤ wcFixed 1 r := by
  haveI := hμ.1
  refine gen_bound one_pos r hr μ hμ (Measure.dirac ()) (fun _ t => F1 μ t)
    (fun t => measurable_const) (Filter.Eventually.of_forall fun _ t =>
      ⟨F1_nonneg μ t, toReal_le_one' μ _⟩)
    (Filter.Eventually.of_forall fun _ t ht => F1_mono μ ht.1) ?_ ?_
  · rw [integral_dirac]; simp
  · intro t ht
    rw [integral_dirac, F2_one μ (hr.1.trans ht.1)]
    simp [phi]

/-- Upper bound over `𝓕_aff` for `n ≥ 2`. -/
theorem ub_aff (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (μ : Measure (Fin n → ℝ))
    (hμ : μ ∈ Faff n) : regret (SPA (Measure.dirac r)) μ ≤ wcFixed n r := by
  have hμA : μ ∈ RobustSPA.Affiliated.Faff n := hμ
  have hFall : μ ∈ Fall n := hμ.1.1
  haveI := hFall.1
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hinv : (1 : ℝ) / n = ((n : ℕ) : ℝ)⁻¹ := one_div _
  refine gen_bound hn0 r hr μ hFall (Measure.dirac ()) (fun _ t => F1 μ t ^ ((1 : ℝ) / n))
    (fun t => measurable_const) (Filter.Eventually.of_forall fun _ t =>
      ⟨Real.rpow_nonneg (F1_nonneg μ t) _,
        Real.rpow_le_one (F1_nonneg μ t) (toReal_le_one' μ _) (by positivity)⟩)
    (Filter.Eventually.of_forall fun _ t ht =>
      Real.rpow_le_rpow (F1_nonneg μ r) (F1_mono μ ht.1) (by positivity)) ?_ ?_
  · rw [integral_dirac, hinv, Real.rpow_inv_natCast_pow (F1_nonneg μ r) (by omega)]
  · intro t _
    rw [integral_dirac]
    have hid := RobustSPA.Affiliated.second_order_stat_identity n hn μ hμA.1 t
    have hl1 := RobustSPA.Affiliated.lemma_1 n hn μ hμA t
    change F2 μ t = (n : ℝ) * RobustSPA.Affiliated.F1k (n - 1) μ t - ((n : ℝ) - 1) * F1 μ t at hid
    change RobustSPA.Affiliated.F1k (n - 1) μ t ^ (1 / ((n : ℝ) - 1)) ≤ F1 μ t ^ (1 / (n : ℝ))
      at hl1
    set y := RobustSPA.Affiliated.F1k (n - 1) μ t with hy
    set z := F1 μ t ^ ((1 : ℝ) / n) with hz
    have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
    have hz0 : 0 ≤ z := Real.rpow_nonneg (F1_nonneg μ t) _
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hyz : y ≤ z ^ (n - 1) := by
      have e : y = (y ^ (1 / ((n : ℝ) - 1))) ^ (n - 1) := by
        rw [← hcast, one_div, Real.rpow_inv_natCast_pow hy0 (by omega)]
      rw [e]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hy0 _) hl1 _
    have hF1z : F1 μ t = z ^ n := by
      rw [hz, hinv, Real.rpow_inv_natCast_pow (F1_nonneg μ t) (by omega)]
    simp only [phi]
    rw [hid, hF1z]
    nlinarith

/-! ### The mixture class -/

lemma cdf_meas (t : ℝ) : Measurable fun G : Measure ℝ => cdfOf G t :=
  (Measure.measurable_coe measurableSet_Iic).ennreal_toReal

lemma cdf_mem (G : Measure ℝ) [IsProbabilityMeasure G] (t : ℝ) : cdfOf G t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, toReal_le_one' G _⟩

lemma cdf_mono (G : Measure ℝ) [IsFiniteMeasure G] : Monotone (cdfOf G) := fun _ _ h =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr h))

lemma cdf_one (G : Measure ℝ) [IsProbabilityMeasure G] (h : G (Set.Icc 0 1)ᶜ = 0) :
    cdfOf G 1 = 1 := by
  have h1 : G (Set.Icc 0 1) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp h
  have : G (Set.Iic 1) = 1 :=
    le_antisymm prob_le_one (h1 ▸ measure_mono (fun x hx => hx.2))
  simp [cdfOf, this]

lemma top_le_iff (hn : 0 < n) (u : Fin n → ℝ) (t : ℝ) : top u ≤ t ↔ ∀ i, u i ≤ t := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le_iff (Finite.bddAbove_range _)

lemma F1_mix (hn : 0 < n) (μ : Measure (Fin n → ℝ)) (M : Measure (Measure ℝ))
    (hcdf : ∀ v : Fin n → ℝ, (μ (Set.Iic v)).toReal = ∫ G, ∏ i, cdfOf G (v i) ∂M) (t : ℝ) :
    F1 μ t = ∫ G, cdfOf G t ^ n ∂M := by
  have : {u : Fin n → ℝ | top u ≤ t} = Set.Iic (fun _ => t) := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_Iic, top_le_iff hn, Pi.le_def]
  rw [F1, this, hcdf]
  simp

lemma isCountablySpanning_Iic_real : IsCountablySpanning (Set.range (Set.Iic : ℝ → Set ℝ)) :=
  ⟨fun k : ℕ => Set.Iic (k : ℝ), fun k => ⟨k, rfl⟩,
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈x⌉₊, Set.mem_Iic.2 (Nat.le_ceil x)⟩⟩

/-- A law on `ℝⁿ` whose CDF is symmetric is exchangeable. -/
lemma exch_of_cdf (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (a : Fin n → ℝ), μ (Set.Iic (a ∘ σ.symm)) = μ (Set.Iic a))
    (σ : Equiv.Perm (Fin n)) : μ.map (fun v => v ∘ σ) = μ := by
  have hf : Measurable (fun v : Fin n → ℝ => v ∘ σ) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  set C : Set (Set (Fin n → ℝ)) := Set.pi Set.univ '' Set.pi Set.univ
    (fun _ : Fin n => Set.range (Set.Iic : ℝ → Set ℝ)) with hC
  have hgen : (inferInstance : MeasurableSpace (Fin n → ℝ)) = MeasurableSpace.generateFrom C :=
    (generateFrom_eq_pi (fun _ => (borel_eq_generateFrom_Iic ℝ).symm.trans
      BorelSpace.measurable_eq.symm) fun _ => isCountablySpanning_Iic_real).symm
  haveI : IsFiniteMeasure (μ.map fun v => v ∘ σ) := Measure.isFiniteMeasure_map _ _
  refine ext_of_generate_finite C hgen (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ ?_
  · rintro s ⟨S, hS, rfl⟩
    choose a ha using fun i => hS i (Set.mem_univ i)
    have hs : Set.pi Set.univ S = Set.Iic a := by
      rw [← Set.pi_univ_Iic]; congr 1; funext i; exact (ha i).symm
    rw [hs, Measure.map_apply hf measurableSet_Iic]
    have : (fun v : Fin n → ℝ => v ∘ σ) ⁻¹' Set.Iic a = Set.Iic (a ∘ σ.symm) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_Iic, Pi.le_def, Function.comp_apply]
      constructor
      · intro h j; simpa using h (σ.symm j)
      · intro h i; simpa using h (σ i)
    rw [this, hsym]
  · rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

lemma mix_exch (μ : Measure (Fin n → ℝ)) (hFall : μ ∈ Fall n) (M : Measure (Measure ℝ))
    (hcdf : ∀ v : Fin n → ℝ, (μ (Set.Iic v)).toReal = ∫ G, ∏ i, cdfOf G (v i) ∂M) :
    μ ∈ RobustSPA.Affiliated.Fexc n := by
  haveI := hFall.1
  refine ⟨hFall, exch_of_cdf μ fun σ a => ?_⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _), hcdf, hcdf]
  congr 1; funext G
  exact Equiv.prod_comp σ.symm (fun i => cdfOf G (a i))

lemma F1k_mix (k : ℕ) (μ : Measure (Fin (k + 1) → ℝ)) (hFall : μ ∈ Fall (k + 1))
    (M : Measure (Measure ℝ))
    (hae : ∀ᵐ G ∂M, IsProbabilityMeasure G ∧ G (Set.Icc 0 1)ᶜ = 0)
    (hcdf : ∀ v : Fin (k + 1) → ℝ, (μ (Set.Iic v)).toReal = ∫ G, ∏ i, cdfOf G (v i) ∂M)
    (t : ℝ) : RobustSPA.Affiliated.F1k (k + 1 - 1) μ t = ∫ G, cdfOf G t ^ k ∂M := by
  set w : Fin (k + 1) → ℝ := fun i => if (i : ℕ) < k then t else 1 with hw
  have hset : {u : Fin (k + 1) → ℝ | ∀ i : Fin (k + 1), (i : ℕ) < k + 1 - 1 → u i ≤ t}
      =ᵐ[μ] Set.Iic w := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null _ hFall.2
      intro u hu hcube
      apply hu.2
      intro i
      simp only [hw]
      split_ifs with h
      · exact hu.1 i (by omega)
      · exact (hcube i (Set.mem_univ _)).2
    · rw [show Set.Iic w \ {u : Fin (k + 1) → ℝ | ∀ i : Fin (k + 1), (i : ℕ) < k + 1 - 1 → u i ≤ t}
          = ∅ from ?_, measure_empty]
      ext u
      simp only [Set.mem_diff, Set.mem_Iic, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_forall]
      intro hu
      push_neg
      intro i hi
      have := hu i
      simp only [hw, if_pos (show (i : ℕ) < k by omega)] at this
      exact this
  unfold RobustSPA.Affiliated.F1k
  rw [measure_congr hset, hcdf]
  apply integral_congr_ae
  filter_upwards [hae] with G hG
  haveI := hG.1
  rw [Fin.prod_univ_castSucc]
  simp only [hw, Fin.coe_castSucc, Fin.is_lt, if_true, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Fin.val_last, lt_irrefl, if_false, cdf_one G hG.2, mul_one]

/-- For `n ≥ 2` and a mixture, `F2 - F1 = ∫ φ(G(t)) dM`. -/
lemma F2F1_mix (hn : 2 ≤ n) (μ : Measure (Fin n → ℝ)) (hFall : μ ∈ Fall n)
    (M : Measure (Measure ℝ)) [IsProbabilityMeasure M]
    (hae : ∀ᵐ G ∂M, IsProbabilityMeasure G ∧ G (Set.Icc 0 1)ᶜ = 0)
    (hcdf : ∀ v : Fin n → ℝ, (μ (Set.Iic v)).toReal = ∫ G, ∏ i, cdfOf G (v i) ∂M) (t : ℝ) :
    F2 μ t - F1 μ t = ∫ G, phi n (cdfOf G t) ∂M := by
  have hex := mix_exch μ hFall M hcdf
  have hF1 := F1_mix (by omega) μ M hcdf t
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hF1k := F1k_mix k μ hFall M hae hcdf t
  have hid := RobustSPA.Affiliated.second_order_stat_identity (k + 1) hn μ hex t
  change F2 μ t = ((k + 1 : ℕ) : ℝ) * RobustSPA.Affiliated.F1k (k + 1 - 1) μ t -
    (((k + 1 : ℕ) : ℝ) - 1) * F1 μ t at hid
  have ib : ∀ m : ℕ, Integrable (fun G : Measure ℝ => cdfOf G t ^ m) M := fun m =>
    Integrable.of_bound ((cdf_meas t).pow_const m).aestronglyMeasurable 1 (by
      filter_upwards [hae] with G hG
      haveI := hG.1
      have h := cdf_mem G t
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h.1 _)]
      exact pow_le_one₀ h.1 h.2)
  rw [hid, hF1k, hF1]
  simp only [phi, show k + 1 - 1 = k by omega]
  rw [integral_sub ((ib k).const_mul _) ((ib (k + 1)).const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- Upper bound over `𝓕_mix` for `n ≥ 2`. -/
theorem ub_mix (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (μ : Measure (Fin n → ℝ))
    (hμ : μ ∈ Fmix n) : regret (SPA (Measure.dirac r)) μ ≤ wcFixed n r := by
  obtain ⟨hFall, M, hM, hae, hcdf⟩ := hμ
  have hn0 : 0 < n := by omega
  refine gen_bound hn0 r hr μ hFall M (fun G t => cdfOf G t) cdf_meas ?_ ?_
    (le_of_eq (F1_mix hn0 μ M hcdf r)) (fun t _ => le_of_eq (F2F1_mix hn μ hFall M hae hcdf t))
  · filter_upwards [hae] with G hG; haveI := hG.1; exact fun t => cdf_mem G t
  · filter_upwards [hae] with G hG; haveI := hG.1; exact fun t ht => cdf_mono G ht.1

end FRP

open FRP RobustSPA.FixedReserve in
theorem solution (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Faff n) :
    regret (SPA (Measure.dirac r)) μ ≤ wcFixed n r :=
  ub_aff hn r hr μ hμ
