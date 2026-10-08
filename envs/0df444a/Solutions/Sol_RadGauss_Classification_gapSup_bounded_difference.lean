-- Prove2me | solution 1 for RadGauss.Classification.gapSup_bounded_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:41:52.41676+00:00
-- url     : https://prove2.me/submissions/c30768c3-5d7b-45fb-b7ea-4f659653dd99

import Mathlib
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

set_option autoImplicit false

lemma gapSup7df_abs_ciSup_sub_le {ι : Type*} (g h : ι → ℝ) (c : ℝ)
    (hg : BddAbove (Set.range g)) (hh : BddAbove (Set.range h))
    (hc : ∀ j, |g j - h j| ≤ c) (hc0 : 0 ≤ c) :
    |(⨆ j, g j) - ⨆ j, h j| ≤ c := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa [ciSup_of_empty] using hc0
  · rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add]
      refine ciSup_le fun j => ?_
      have := (abs_sub_le_iff.mp (hc j)).1
      have h2 := le_ciSup hh j
      linarith
    · rw [sub_le_iff_le_add]
      refine ciSup_le fun j => ?_
      have := (abs_sub_le_iff.mp (hc j)).2
      have h2 := le_ciSup hg j
      linarith

lemma gapSup7df_card_le {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (i : Fin n) (hpq : ∀ j, j ≠ i → (p j ↔ q j)) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card + 1 := by
  calc (Finset.univ.filter p).card ≤ (insert i (Finset.univ.filter q)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_cases hji : j = i
        · simp [hji]
        · simp [(hpq j hji).1 hj]
    _ ≤ _ := Finset.card_insert_le _ _

lemma gapSup7df_train {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (i : Fin n) (z' : X × ℤˣ)
    (f : X → ℤˣ) :
    |RadGauss.Classification.trainError S f
      - RadGauss.Classification.trainError (Function.update S i z') f| ≤ 1 / (n : ℝ) := by
  unfold RadGauss.Classification.trainError
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  have hpq : ∀ j, j ≠ i → ((S j).2 ≠ f (S j).1 ↔
      (Function.update S i z' j).2 ≠ f (Function.update S i z' j).1) := by
    intro j hj
    rw [Function.update_of_ne hj]
  have h1 := gapSup7df_card_le _ _ i hpq
  have h2 := gapSup7df_card_le _ _ i (fun j hj => (hpq j hj).symm)
  rw [← sub_div, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  rw [abs_sub_le_iff]
  constructor
  · have : ((Finset.univ.filter fun j => (S j).2 ≠ f (S j).1).card : ℝ) ≤
        ((Finset.univ.filter fun j =>
          (Function.update S i z' j).2 ≠ f (Function.update S i z' j).1).card : ℝ) + 1 := by
      exact_mod_cast h1
    linarith
  · have : ((Finset.univ.filter fun j =>
          (Function.update S i z' j).2 ≠ f (Function.update S i z' j).1).card : ℝ) ≤
        ((Finset.univ.filter fun j => (S j).2 ≠ f (S j).1).card : ℝ) + 1 := by
      exact_mod_cast h2
    linarith

lemma gapSup7df_bdd {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) {n : ℕ}
    (S : Fin n → X × ℤˣ) :
    BddAbove (Set.range fun f : F =>
      RadGauss.Classification.classError P f - RadGauss.Classification.trainError S f) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨f, rfl⟩
  have h1 : RadGauss.Classification.classError P f ≤ 1 := by
    unfold RadGauss.Classification.classError
    exact measureReal_le_one
  have h2 : 0 ≤ RadGauss.Classification.trainError S f := by
    unfold RadGauss.Classification.trainError
    positivity
  simp only
  linarith

open MeasureTheory RadGauss.Classification in
theorem solution {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) {n : ℕ}
    (S : Fin n → X × ℤˣ) (i : Fin n) (z' : X × ℤˣ) :
    |gapSup P F S - gapSup P F (Function.update S i z')| ≤ 1 / (n : ℝ) := by
  unfold gapSup
  apply gapSup7df_abs_ciSup_sub_le _ _ _ (gapSup7df_bdd P F S)
    (gapSup7df_bdd P F (Function.update S i z'))
  · intro f
    have := gapSup7df_train S i z' (f : X → ℤˣ)
    rw [show classError P f - trainError S f - (classError P f - trainError (Function.update S i z') f)
      = -(trainError S f - trainError (Function.update S i z') f) by ring, abs_neg]
    exact this
  · positivity
