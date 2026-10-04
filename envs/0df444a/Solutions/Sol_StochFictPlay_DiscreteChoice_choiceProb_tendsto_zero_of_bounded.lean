-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.choiceProb_tendsto_zero_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:24:21.809984+00:00
-- url     : https://prove2.me/submissions/3dbea41c-5f29-4072-9120-00734e63801f

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

open Filter Topology MeasureTheory

namespace StochFictPlay.DiscreteChoice.AuxE1

lemma noiseLaw_univ {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f) :
    noiseLaw f Set.univ = 1 := by
  rw [noiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hf.lintegral_eq_one

lemma noiseLaw_ne_top {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (s : Set (Fin n → ℝ)) : noiseLaw f s ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ s))
  rw [noiseLaw_univ f hf]
  exact ENNReal.one_ne_top

lemma tail_tendsto {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (i j : Fin n) :
    Tendsto (fun t : ℝ => noiseLaw f {e | t < e j - e i}) atTop (𝓝 0) := by
  have hmeas : ∀ t : ℝ, MeasurableSet {e : Fin n → ℝ | t < e j - e i} := fun t =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).sub (measurable_pi_apply i))
  have hanti : Antitone (fun t : ℝ => {e : Fin n → ℝ | t < e j - e i}) := by
    intro a b hab e he
    exact lt_of_le_of_lt hab he
  have hfin : ∃ t : ℝ, noiseLaw f {e : Fin n → ℝ | t < e j - e i} ≠ ⊤ :=
    ⟨0, noiseLaw_ne_top f hf _⟩
  have h := tendsto_measure_iInter_atTop (μ := noiseLaw f)
    (fun t => (hmeas t).nullMeasurableSet) hanti hfin
  have hempty : (⋂ t : ℝ, {e : Fin n → ℝ | t < e j - e i}) = ∅ := by
    ext e
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    exact ⟨e j - e i, le_refl _⟩
  rw [hempty, measure_empty] at h
  exact h

end StochFictPlay.DiscreteChoice.AuxE1

open Filter Topology StochFictPlay.DiscreteChoice in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (J : Finset (Fin n)) (hJ : Jᶜ.Nonempty)
    (π : ℕ → Fin n → ℝ) (hbdd : ∃ B : ℝ, ∀ k, ∀ j ∈ J, |π k j| ≤ B)
    (htop : ∀ i ∉ J, Tendsto (fun k => π k i) atTop atTop) :
    ∀ j ∈ J, Tendsto (fun k => choiceProb f (π k) j) atTop (𝓝 0) := by
  intro j hj
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨i, hi⟩ := hJ
  have hiJ : i ∉ J := Finset.mem_compl.mp hi
  have hij : i ≠ j := fun h => hiJ (h ▸ hj)
  have ht : Tendsto (fun k => π k i - B) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-B) (htop i hiJ)
  have hT := (StochFictPlay.DiscreteChoice.AuxE1.tail_tendsto f hf i j).comp ht
  have hT' : Tendsto (fun k => (noiseLaw f {e | π k i - B < e j - e i}).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT'
    (fun k => ENNReal.toReal_nonneg) (fun k => ?_)
  unfold choiceProb
  apply ENNReal.toReal_mono (StochFictPlay.DiscreteChoice.AuxE1.noiseLaw_ne_top f hf _)
  apply measure_mono
  intro e he
  have h1 := he i hij
  have h2 := (abs_le.mp (hB k j hj)).2
  show π k i - B < e j - e i
  linarith
