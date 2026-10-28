-- Prove2me | solution 1 for RobustSPA.IID.SPA_isDSIC
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:06:51.511806+00:00
-- url     : https://prove2.me/submissions/830e8f7b-9d6e-423e-9e78-3ad185138943

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting
open MeasureTheory
open scoped Classical

namespace RSPA2DSIC
open RobustSPA.IID

variable {n : ℕ}

lemma SPA_x (ρ : Measure ℝ) (i : Fin n) (v : Fin n → ℝ) :
    (SPA (n := n) ρ).x i v = if isWinner v i then (ρ (Set.Iic (v i))).toReal else 0 := rfl

lemma SPA_p (ρ : Measure ℝ) (i : Fin n) (v : Fin n → ℝ) :
    (SPA (n := n) ρ).p i v = if isWinner v i then
      ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ else 0 := rfl

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

lemma cmax_update (v : Fin n → ℝ) (i : Fin n) (w : ℝ) :
    cmax (Function.update v i w) i = cmax v i := by
  unfold cmax
  congr 1
  funext j
  exact Function.update_of_ne j.2 _ _

lemma cmax_le_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) (h0 : 0 ≤ v i) :
    cmax v i ≤ v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · exact ciSup_le (fun j => hw.1 j)
  · haveI : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    unfold cmax; rw [Real.iSup_of_isEmpty]; exact h0

lemma le_cmax_of_not_winner {v : Fin n → ℝ} {i : Fin n} (hw : ¬ isWinner v i) :
    v i ≤ cmax v i := by
  unfold isWinner at hw
  by_cases h : ∀ j, v j ≤ v i
  · have : ¬ ∀ j, j < i → v j < v i := fun h' => hw ⟨h, h'⟩
    push_neg at this
    obtain ⟨j, hji, hj⟩ := this
    exact hj.trans (le_cmax v i j (ne_of_lt hji))
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    have hne : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
    exact hj.le.trans (le_cmax v i j hne)

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

/-- integrability of the bounded integrands -/
lemma integrable_ind_max (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c : ℝ) :
    Integrable (fun q => (Set.Iic a).indicator (fun q => max c q) q) ρ := by
  refine Integrable.of_bound ((measurable_const.max measurable_id).indicator
    measurableSet_Iic).aestronglyMeasurable (|c| + |a|) (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ Set.Iic a
  · rw [Set.indicator_of_mem hq, Real.norm_eq_abs, abs_le]
    have : q ≤ a := hq
    constructor
    · have := neg_abs_le c; have := abs_nonneg a; have := le_max_left c q; linarith
    · have := le_abs_self c; have := le_abs_self a; have := abs_nonneg c; have := abs_nonneg a
      rcases le_total c q with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  · rw [Set.indicator_of_notMem hq]; simp; positivity

lemma util_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c val : ℝ) :
    val * (ρ (Set.Iic a)).toReal - ∫ q, (Set.Iic a).indicator (fun q => max c q) q ∂ρ
      = ∫ q, (Set.Iic a).indicator (fun q => val - max c q) q ∂ρ := by
  have h1 : (fun q => (Set.Iic a).indicator (fun q => val - max c q) q)
      = fun q => (Set.Iic a).indicator (fun _ => val) q
          - (Set.Iic a).indicator (fun q => max c q) q := by
    funext q
    by_cases hq : q ∈ Set.Iic a
    · simp [Set.indicator_of_mem hq]
    · simp [Set.indicator_of_notMem hq]
  rw [h1, integral_sub ((integrable_const val).indicator measurableSet_Iic)
    (integrable_ind_max ρ a c), integral_indicator_const _ measurableSet_Iic, smul_eq_mul,
    measureReal_def, mul_comm]

lemma ind_le_ind {a c val q : ℝ} (hc : c ≤ val) :
    (Set.Iic a).indicator (fun q => val - max c q) q
      ≤ (Set.Iic val).indicator (fun q => val - max c q) q := by
  by_cases hqa : q ≤ a <;> by_cases hqv : q ≤ val
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa),
      Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa),
      Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]
    push_neg at hqv
    have := le_max_right c q; linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa),
      Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
    have : max c q ≤ val := max_le hc hqv
    linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa),
      Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]

lemma ind_nonpos {a c val q : ℝ} (hc : val ≤ c) :
    (Set.Iic a).indicator (fun q => val - max c q) q ≤ 0 := by
  by_cases hqa : q ≤ a
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic a from hqa)]
    have := le_max_left c q; linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic a from hqa)]

lemma ind_nonneg {c val q : ℝ} (hc : c ≤ val) :
    0 ≤ (Set.Iic val).indicator (fun q => val - max c q) q := by
  by_cases hqv : q ≤ val
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic val from hqv)]
    have : max c q ≤ val := max_le hc hqv
    linarith
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic val from hqv)]

lemma integrable_ind_sub (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a c val : ℝ) :
    Integrable (fun q => (Set.Iic a).indicator (fun q => val - max c q) q) ρ := by
  have h1 : (fun q => (Set.Iic a).indicator (fun q => val - max c q) q)
      = fun q => (Set.Iic a).indicator (fun _ => val) q
          - (Set.Iic a).indicator (fun q => max c q) q := by
    funext q
    by_cases hq : q ∈ Set.Iic a
    · simp [Set.indicator_of_mem hq]
    · simp [Set.indicator_of_notMem hq]
  rw [h1]
  exact ((integrable_const val).indicator measurableSet_Iic).sub (integrable_ind_max ρ a c)

/-- truthful utility of buyer `i` is nonnegative, and equals this integral when `i` wins -/
lemma truthful_util (ρ : Measure ℝ) [IsFiniteMeasure ρ] (v : Fin n → ℝ) (hv : v ∈ cube n)
    (i : Fin n) :
    0 ≤ v i * (SPA (n := n) ρ).x i v - (SPA (n := n) ρ).p i v := by
  rw [SPA_x, SPA_p]
  by_cases hw : isWinner v i
  · rw [if_pos hw, if_pos hw, util_eq, second_eq_cmax hw]
    exact integral_nonneg (fun q => ind_nonneg (cmax_le_of_winner hw (hv i (Set.mem_univ _)).1))
  · rw [if_neg hw, if_neg hw]; simp

lemma meas_winner (i : Fin n) : MeasurableSet {v : Fin n → ℝ | isWinner v i} := by
  unfold isWinner
  refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun j => ?_)
    (Measurable.forall fun j => Measurable.imp measurable_const ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))
  · exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))

lemma meas_second : Measurable (fun v : Fin n → ℝ => second v) := by
  unfold second
  exact Measurable.iSup (fun q => (measurable_pi_apply _).min (measurable_pi_apply _))

theorem SPA_isDSIC' (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (SPA (n := n) ρ).IsDSIC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v _ i
    rw [SPA_x]
    split_ifs
    · refine ⟨ENNReal.toReal_nonneg, ?_⟩
      have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := Set.Iic (v i)))
      simpa using this
    · exact ⟨le_refl _, zero_le_one⟩
  · intro v hv i
    exact truthful_util ρ v hv i
  · intro v hv i w hw
    have htr := truthful_util ρ v hv i
    rw [SPA_x, SPA_p]
    by_cases hw' : isWinner (Function.update v i w) i
    · rw [if_pos hw', if_pos hw', second_eq_cmax hw', cmax_update, Function.update_self, util_eq]
      by_cases hvw : isWinner v i
      · rw [SPA_x, SPA_p, if_pos hvw, if_pos hvw, util_eq, second_eq_cmax hvw]
        exact integral_mono (integrable_ind_sub ρ _ _ _) (integrable_ind_sub ρ _ _ _)
          (fun q => ind_le_ind (cmax_le_of_winner hvw (hv i (Set.mem_univ _)).1))
      · rw [SPA_x, SPA_p, if_neg hvw, if_neg hvw]
        simp only [mul_zero, sub_zero]
        exact integral_nonpos (fun q => ind_nonpos (le_cmax_of_not_winner hvw))
    · rw [if_neg hw', if_neg hw']
      simpa using htr
  · intro v _
    by_cases h : ∃ i, isWinner v i
    · obtain ⟨i0, h0⟩ := h
      rw [Finset.sum_eq_single i0 (fun j _ hj => by
        rw [SPA_x, if_neg (fun hw => hj (isWinner_unique hw h0))])
        (fun h => absurd (Finset.mem_univ i0) h)]
      rw [SPA_x, if_pos h0]
      have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := Set.Iic (v i0)))
      simpa using this
    · push_neg at h
      rw [Finset.sum_eq_zero (fun j _ => by rw [SPA_x, if_neg (h j)])]
      exact zero_le_one
  · intro i
    have hmono : Monotone (fun a : ℝ => (ρ (Set.Iic a)).toReal) := fun a b hab =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))
    exact Measurable.ite (meas_winner i) (hmono.measurable.comp (measurable_pi_apply i))
      measurable_const
  · intro i
    refine Measurable.ite (meas_winner i) ?_ measurable_const
    have hf : StronglyMeasurable (Function.uncurry fun (v : Fin n → ℝ) (q : ℝ) =>
        (Set.Iic (v i)).indicator (fun q => max (second v) q) q) := by
      apply Measurable.stronglyMeasurable
      change Measurable (fun z : (Fin n → ℝ) × ℝ =>
        (Set.Iic (z.1 i)).indicator (fun q => max (second z.1) q) z.2)
      simp only [Set.indicator_apply, Set.mem_Iic]
      exact Measurable.ite (measurableSet_le measurable_snd
        ((measurable_pi_apply i).comp measurable_fst))
        ((meas_second.comp measurable_fst).max measurable_snd) measurable_const
    exact (hf.integral_prod_right (ν := ρ)).measurable
  · refine ⟨1, fun v hv i => ?_⟩
    rw [SPA_p]
    split_ifs
    · have := norm_integral_le_of_norm_le_const (μ := ρ)
        (f := fun q => (Set.Iic (v i)).indicator (fun q => max (second v) q) q) (C := 1)
        (Filter.Eventually.of_forall fun q => ?_)
      · simpa using this
      · have h0 := second_nonneg hv
        have h1 := second_le_one hv
        have hvi := (hv i (Set.mem_univ _)).2
        by_cases hq : q ≤ v i
        · rw [Set.indicator_of_mem (show q ∈ Set.Iic (v i) from hq), Real.norm_eq_abs, abs_le]
          constructor
          · have := le_max_left (second v) q; linarith
          · exact max_le h1 (hq.trans hvi)
        · rw [Set.indicator_of_notMem (show q ∉ Set.Iic (v i) from hq)]; simp
    · simp

end RSPA2DSIC

theorem solution (n : ℕ) (ρ : ProbabilityMeasure ℝ) :
    (RobustSPA.IID.SPA (n := n) (ρ : Measure ℝ)).IsDSIC :=
  RSPA2DSIC.SPA_isDSIC' (ρ : Measure ℝ)
