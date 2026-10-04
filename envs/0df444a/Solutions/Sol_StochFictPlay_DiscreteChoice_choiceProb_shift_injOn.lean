-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.choiceProb_shift_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:57:31.309606+00:00
-- url     : https://prove2.me/submissions/cfdba90d-4639-4cdb-84f3-e0b8da646cbb

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex

set_option autoImplicit false

open MeasureTheory

namespace StochFictPlay.DiscreteChoice.E02F

lemma noiseLaw_le_one {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (s : Set (Fin n → ℝ)) : noiseLaw f s ≠ ⊤ := by
  have h1 : noiseLaw f Set.univ = 1 := by
    unfold noiseLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hf.lintegral_eq_one
  refine ne_top_of_le_ne_top (b := noiseLaw f Set.univ) ?_ (measure_mono (Set.subset_univ s))
  rw [h1]; exact ENNReal.one_ne_top

lemma noiseLaw_pos {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (s : Set (Fin n → ℝ)) (hs : IsOpen s) (hne : s.Nonempty) : noiseLaw f s ≠ 0 := by
  unfold noiseLaw
  have hm : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf.continuous.measurable
  rw [Ne, withDensity_apply_eq_zero hm]
  have : {x | ENNReal.ofReal (f x) ≠ 0} ∩ s = s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le,
      and_iff_right_iff_imp]
    intro _; exact hf.pos x
  rw [this]
  exact (hs.measure_pos volume hne).ne'

lemma isOpen_event {n : ℕ} (π : Fin n → ℝ) (i : Fin n) :
    IsOpen {e : Fin n → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i} := by
  have : {e : Fin n → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i} =
      ⋂ j, {e : Fin n → ℝ | j ≠ i → π j + e j < π i + e i} := by
    ext e; simp
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases h : j = i
  · simp [h]
  · simp only [ne_eq, h, not_false_eq_true, forall_const]
    exact isOpen_lt (continuous_const.add (continuous_apply j))
      (continuous_const.add (continuous_apply i))

end StochFictPlay.DiscreteChoice.E02F

open StochFictPlay.DiscreteChoice.E02F in
open MeasureTheory in
open StochFictPlay.DiscreteChoice in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) :
    (∀ (π : Fin n → ℝ) (c : ℝ), choiceProb f (π + fun _ => c) = choiceProb f π) ∧
      Set.InjOn (choiceProb f) (tangentSpace n : Set (Fin n → ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro π c
    funext i
    unfold choiceProb
    congr 2
    ext e
    simp only [Set.mem_ofPred_eq, Pi.add_apply]
    constructor
    · intro h j hj; have := h j hj; linarith
    · intro h j hj; have := h j hj; linarith
  · intro π hπ π' hπ' hEq
    by_contra hne
    have hs : ∑ j, π j = 0 := hπ
    have hs' : ∑ j, π' j = 0 := hπ'
    set d : Fin n → ℝ := fun j => π j - π' j with hd
    obtain ⟨j0, -⟩ := Function.ne_iff.mp hne
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ d ⟨j0, Finset.mem_univ _⟩
    have hk : ∃ k, d k < d i := by
      by_contra hno
      push_neg at hno
      have hall : ∀ j, d j = d i := fun j => le_antisymm (hi j (Finset.mem_univ _)) (hno j)
      have hsum : ∑ j, d j = 0 := by
        simp only [hd, Finset.sum_sub_distrib, hs, hs', sub_zero]
      rw [Finset.sum_congr rfl (fun j _ => hall j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hsum
      have hn : (n : ℝ) ≠ 0 := by
        have : 0 < n := Fin.pos j0
        exact_mod_cast this.ne'
      have hdi : d i = 0 := by
        rcases mul_eq_zero.mp hsum with h | h
        · exact absurd h hn
        · exact h
      apply hne
      funext j
      have := hall j
      simp only [hd] at this hdi
      linarith
    obtain ⟨k, hk⟩ := hk
    have hki : k ≠ i := by rintro rfl; exact lt_irrefl _ hk
    -- events
    set A := {e : Fin n → ℝ | ∀ j, j ≠ i → π j + e j < π i + e i} with hA
    set A' := {e : Fin n → ℝ | ∀ j, j ≠ i → π' j + e j < π' i + e i} with hA'
    set D := A ∩ {e : Fin n → ℝ | π' i + e i < π' k + e k} with hD
    have hDopen : IsOpen D := (isOpen_event π i).inter
      (isOpen_lt (continuous_const.add (continuous_apply i))
        (continuous_const.add (continuous_apply k)))
    have hdik : π' i - π' k < π i - π k := by
      have := hk; simp only [hd] at this; linarith
    set t : ℝ := ((π i - π k) + (π' i - π' k)) / 2 with ht
    have hDne : D.Nonempty := by
      refine ⟨fun j => if j = i then 0 else if j = k then t else π i - π j - 1, ?_, ?_⟩
      · intro j hj
        simp only [hj, if_false, if_true]
        by_cases hjk : j = k
        · subst hjk; simp only [if_true]; linarith
        · simp only [hjk, if_false]; linarith
      · simp only [Set.mem_ofPred_eq, if_true, hki, if_false]
        linarith
    have hsub : A' ∪ D ⊆ A := by
      rintro e (he | he)
      · intro j hj
        have h1 := he j hj
        have h2 := hi j (Finset.mem_univ _)
        simp only [hd] at h2
        linarith
      · exact he.1
    have hdisj : Disjoint A' D := by
      rw [Set.disjoint_left]
      intro e he heD
      have h1 : π' k + e k < π' i + e i := he k hki
      have h2 : π' i + e i < π' k + e k := heD.2
      linarith
    have hlt : noiseLaw f A' < noiseLaw f A := by
      calc noiseLaw f A' < noiseLaw f A' + noiseLaw f D :=
            ENNReal.lt_add_right (noiseLaw_le_one f hf A') (noiseLaw_pos f hf D hDopen hDne)
        _ = noiseLaw f (A' ∪ D) := (measure_union hdisj hDopen.measurableSet).symm
        _ ≤ noiseLaw f A := measure_mono hsub
    have hreal : (noiseLaw f A').toReal < (noiseLaw f A).toReal :=
      (ENNReal.toReal_lt_toReal (noiseLaw_le_one f hf A') (noiseLaw_le_one f hf A)).mpr hlt
    have := congrFun hEq i
    unfold choiceProb at this
    rw [← hA, ← hA'] at this
    linarith
