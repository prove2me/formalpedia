-- Prove2me | solution 2 for PrefSemimetric.TopDiff.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:41:08.164593+00:00
-- url     : https://prove2.me/submissions/4d29d17d-6816-4a49-9d49-78daf0ba4dfd

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model
set_option autoImplicit false

open PrefSemimetric.TopDiff

lemma zzb_ominus_asymm {X : Type*} (R : X → X → Prop) (a b : X) (hab : asymmPart R a b) (y x : X) :
    asymmPart (ominus R a b) y x ↔ asymmPart R y x ∧ ¬ (y = a ∧ x = b) := by
  obtain ⟨hRab, hRba⟩ := hab
  simp only [asymmPart, ominus]
  by_cases hy : y = a <;> by_cases hx : x = b <;> by_cases h1 : R y x <;> by_cases h2 : R x y <;>
    simp_all <;> aesop

lemma zzb_oplus_asymm {X : Type*} (R : X → X → Prop) (a b : X) (h1 : ¬ asymmPart R a b)
    (h2 : ¬ asymmPart R b a) (hne : a ≠ b) (y x : X) :
    asymmPart (oplus R a b) y x ↔ asymmPart R y x ∨ (y = a ∧ x = b) := by
  simp only [asymmPart, oplus] at *
  by_cases hy : y = a <;> by_cases hx : x = b <;> by_cases h3 : R y x <;> by_cases h4 : R x y <;>
    simp_all <;> aesop

lemma zzb_prop_aux (P Q C : Prop) (h : (P ↔ C) → (Q ↔ P)) :
    (((P ∧ ¬Q) ∨ (Q ∧ ¬P)) ∨ ((Q ∧ ¬C) ∨ (C ∧ ¬Q))) ↔ ((P ∧ ¬C) ∨ (C ∧ ¬P)) := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hc : C <;> simp_all

lemma zzb_prop_aux2 (P Q C : Prop) (h : (P ↔ C) → (Q ↔ P)) :
    ¬ (((P ∧ ¬Q) ∨ (Q ∧ ¬P)) ∧ ((Q ∧ ¬C) ∨ (C ∧ ¬Q))) := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hc : C <;> simp_all

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T)
    (h : OneStepToward R R0 T) (S : Finset X) :
    Disjoint (symmDiff (maxSet S R) (maxSet S R0)) (symmDiff (maxSet S R0) (maxSet S T)) ∧
      symmDiff (maxSet S R) (maxSet S R0) ∪ symmDiff (maxSet S R0) (maxSet S T) =
        symmDiff (maxSet S R) (maxSet S T) := by
  obtain ⟨_, hstep⟩ := h
  have key : ∀ x, (x ∈ maxSet S R ↔ x ∈ maxSet S T) → (x ∈ maxSet S R0 ↔ x ∈ maxSet S R) := by
    intro x hRT
    simp only [maxSet, Finset.mem_filter] at hRT ⊢
    rcases hstep with ⟨a, b, hab, rfl, hnT, hTR⟩ | ⟨a, b, h1, h2, rfl, hT'⟩
    · simp only [zzb_ominus_asymm R a b hab]
      constructor
      · rintro ⟨hxS, h0⟩
        refine ⟨hxS, fun y hy hy' => ?_⟩
        by_cases hc : y = a ∧ x = b
        · obtain ⟨hya, hxb⟩ := hc
          have hnmem : ¬ (x ∈ S ∧ ∀ z ∈ S, ¬ asymmPart R z x) := fun hh => hh.2 y hy hy'
          have hex : ∃ z ∈ S, asymmPart T z x := by
            by_contra hne
            push_neg at hne
            exact hRT.not.mp hnmem ⟨hxS, hne⟩ |>.elim
          obtain ⟨z, hzS, hzT⟩ := hex
          have hzR : asymmPart R z x := by rw [hxb] at hzT ⊢; exact hTR z hzT
          refine h0 z hzS ⟨hzR, ?_⟩
          rintro ⟨hza, _⟩
          apply hnT
          rw [← hza, ← hxb]
          exact hzT
        · exact h0 y hy ⟨hy', hc⟩
      · rintro ⟨hxS, h0⟩
        exact ⟨hxS, fun y hy hy' => h0 y hy hy'.1⟩
    · have hne : a ≠ b := fun hab => by subst hab; exact hT'.2 hT'.1
      simp only [zzb_oplus_asymm R a b h1 h2 hne]
      constructor
      · rintro ⟨hxS, h0⟩
        exact ⟨hxS, fun y hy hy' => h0 y hy (Or.inl hy')⟩
      · rintro ⟨hxS, hR'⟩
        refine ⟨hxS, fun y hy hy' => ?_⟩
        rcases hy' with hy' | ⟨hya, hxb⟩
        · exact hR' y hy hy'
        · have hT2 := (hRT.mp ⟨hxS, hR'⟩).2 y hy
          apply hT2
          rw [hya, hxb]
          exact hT'
  constructor
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_symmDiff] at hx1 hx2
    exact zzb_prop_aux2 _ _ _ (key x) ⟨hx1, hx2⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_symmDiff]
    exact zzb_prop_aux _ _ _ (key x)
