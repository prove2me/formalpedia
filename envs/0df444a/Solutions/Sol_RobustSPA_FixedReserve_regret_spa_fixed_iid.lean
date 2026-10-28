-- Prove2me | solution 1 for RobustSPA.FixedReserve.regret_spa_fixed_iid
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:03:53.770665+00:00
-- url     : https://prove2.me/submissions/d04b5b0c-bf0b-49f4-82fd-a954ea2488e3

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

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

lemma top_le_iff (hn : 0 < n) (u : Fin n → ℝ) (t : ℝ) : top u ≤ t ↔ ∀ i, u i ≤ t := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le_iff (Finite.bddAbove_range _)


lemma dirac_one_cdf {t : ℝ} (ht : t < 1) : cdfOf (Measure.dirac (1 : ℝ)) t = 0 := by
  simp [cdfOf, Measure.dirac_apply' _ measurableSet_Iic, Set.indicator, not_le.mpr ht]

end FRP

open FRP RobustSPA.FixedReserve in
theorem solution : ¬ (∀ (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (G : ProbabilityMeasure ℝ) (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0),
    regret (SPA (Measure.dirac r)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
      r * ((G : Measure ℝ) (Set.Iio r)).toReal ^ n
        - ∫ v in (0)..r, cdfOf (G : Measure ℝ) v ^ n
        + ∫ v in r..1, ((n : ℝ) * cdfOf (G : Measure ℝ) v ^ (n - 1)
            - (n : ℝ) * cdfOf (G : Measure ℝ) v ^ n)) := by
  intro h
  set G : ProbabilityMeasure ℝ := ⟨Measure.dirac 1, inferInstance⟩ with hGdef
  have hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := by
    show Measure.dirac (1 : ℝ) (Set.Icc 0 1)ᶜ = 0
    simp [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator]
  have hr : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have H := h 1 one_pos (1 / 2) hr G hG
  have hGc : ∀ t : ℝ, t < 1 → cdfOf (G : Measure ℝ) t = 0 := fun t ht => dirac_one_cdf ht
  set μ : Measure (Fin 1 → ℝ) := Measure.pi fun _ : Fin 1 => (G : Measure ℝ) with hμ
  haveI : IsProbabilityMeasure (G : Measure ℝ) := inferInstance
  have hFall : μ ∈ Fall 1 := by
    refine ⟨inferInstance, ?_⟩
    show μ (Set.univ.pi fun _ => Set.Icc 0 1)ᶜ = 0
    rw [prob_compl_eq_zero_iff (MeasurableSet.univ_pi fun _ => measurableSet_Icc), hμ,
      Measure.pi_pi]
    show ∏ _i : Fin 1, Measure.dirac (1 : ℝ) (Set.Icc 0 1) = 1
    simp [Measure.dirac_apply' _ measurableSet_Icc, Set.indicator]
  haveI := hFall.1
  -- left-hand side is 1/2
  have hF1 : ∀ t : ℝ, t < 1 → F1 μ t = 0 := by
    intro t ht
    have : {u : Fin 1 → ℝ | top u ≤ t} = Set.univ.pi fun _ => Set.Iic t := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic,
        top_le_iff one_pos]
    rw [F1, this, hμ, Measure.pi_pi, ENNReal.toReal_prod]
    simp only [Finset.univ_unique, Finset.prod_singleton]
    exact hGc t ht
  have hLHS : regret (SPA (Measure.dirac (1 / 2 : ℝ))) μ = 1 / 2 := by
    rw [regret_fixed_formula one_pos _ hr μ hFall]
    have hP : (μ {v | top v < 1 / 2}).toReal = 0 := by
      have h0 : (μ {v : Fin 1 → ℝ | top v ≤ 1 / 2}).toReal = 0 := hF1 _ (by norm_num)
      have := ENNReal.toReal_mono (measure_ne_top μ {v : Fin 1 → ℝ | top v ≤ 1 / 2})
        (measure_mono (μ := μ) fun v (hv : top v < 1 / 2) => (le_of_lt hv : top v ≤ 1 / 2))
      have h1 : 0 ≤ (μ {v | top v < 1 / 2}).toReal := ENNReal.toReal_nonneg
      exact le_antisymm (this.trans h0.le) h1
    have hI1 : ∫ t in (0 : ℝ)..1 / 2, F1 μ t = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
        setIntegral_congr_fun measurableSet_Ico (g := fun _ => (0 : ℝ))
          (fun t ht => hF1 t (by linarith [ht.2]))]
      simp
    have hI2 : ∫ t in (1 / 2 : ℝ)..1, (F2 μ t - F1 μ t) = 1 / 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
        setIntegral_congr_fun measurableSet_Ico (g := fun _ => (1 : ℝ))
          (fun t ht => by
            simp only
            rw [F2_one μ (by linarith [ht.1]), hF1 t ht.2]; ring),
        setIntegral_const, vol_Ico _ _ (by norm_num)]
      norm_num
    rw [hP, hI1, hI2]; ring
  -- right-hand side is -1/4
  have hC : ∫ v in (1 / 2 : ℝ)..1, (((1 : ℕ) : ℝ) * cdfOf (G : Measure ℝ) v ^ (1 - 1)
      - ((1 : ℕ) : ℝ) * cdfOf (G : Measure ℝ) v ^ 1) = 1 / 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Ico (g := fun _ => (1 : ℝ))
        (fun t ht => by simp only; rw [hGc t ht.2]; norm_num),
      setIntegral_const, vol_Ico _ _ (by norm_num)]
    norm_num
  have hIio : ((G : Measure ℝ) (Set.Iio (1 / 2))).toReal = 0 := by
    show (Measure.dirac (1 : ℝ) (Set.Iio (1 / 2))).toReal = 0
    simp [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator]
    norm_num
  have hRHS : ∫ v in (0 : ℝ)..1 / 2, (cdfOf (G : Measure ℝ) v ^ 1 +
      ∫ v in (1 / 2 : ℝ)..1, (((1 : ℕ) : ℝ) * cdfOf (G : Measure ℝ) v ^ (1 - 1)
        - ((1 : ℕ) : ℝ) * cdfOf (G : Measure ℝ) v ^ 1)) = 1 / 4 := by
    rw [hC, intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
      setIntegral_congr_fun measurableSet_Ico (g := fun _ => (1 / 2 : ℝ))
        (fun t ht => by simp only; rw [hGc t (by linarith [ht.2])]; norm_num),
      setIntegral_const, vol_Ico _ _ (by norm_num)]
    norm_num
  rw [hLHS, hIio] at H
  rw [hRHS] at H
  norm_num at H
