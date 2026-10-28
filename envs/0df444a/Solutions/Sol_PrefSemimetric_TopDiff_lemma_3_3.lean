-- Prove2me | solution 1 for PrefSemimetric.TopDiff.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:01:34.401608+00:00
-- url     : https://prove2.me/submissions/e3e09ac0-67ec-44eb-9b1e-3fa322626308

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem ps_mem_max {X : Type*} (S : Finset X) (R : X → X → Prop) (x : X) :
    x ∈ maxSet S R ↔ x ∈ S ∧ ∀ y ∈ S, ¬ asymmPart R y x := by
  unfold maxSet; simp [Finset.mem_filter]

theorem ps_key {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hT : IsAcyclicOrder T)
    (h : OneStepToward R R0 T) (S : Finset X) (x : X) :
    ¬ (x ∈ symmDiff (maxSet S R) (maxSet S R0) ∧ x ∈ symmDiff (maxSet S R0) (maxSet S T)) := by
  obtain ⟨_, h⟩ := h
  simp only [Finset.mem_symmDiff]
  rcases h with ⟨a, b, hRab, rfl, hTab, hTx⟩ | ⟨a, b, hRab, hRba, rfl, hTab⟩
  · have hasym : ∀ y z, asymmPart (ominus R a b) y z ↔ asymmPart R y z ∧ ¬ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, ominus]
      obtain ⟨hr1, hr2⟩ := hRab
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    have hne : x ≠ b → (x ∈ maxSet S R ↔ x ∈ maxSet S (ominus R a b)) := by
      intro hxb
      rw [ps_mem_max, ps_mem_max]
      simp only [hasym]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy hh.1⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy ⟨hh, fun e => hxb e.2⟩⟩
    have h10 : x ∈ maxSet S R → x ∈ maxSet S (ominus R a b) := by
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy hh.1⟩
    have h0T : x = b → x ∈ maxSet S (ominus R a b) → x ∈ maxSet S T := by
      rintro rfl
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy hyT => ?_⟩
      have hya : y ≠ a := by rintro rfl; exact hTab hyT
      exact h y hy ⟨hTx y hyT, fun e => hya e.1⟩
    by_cases hxb : x = b
    · have := h0T hxb; tauto
    · have := hne hxb; tauto
  · have hab : a ≠ b := by
      rintro rfl; exact hTab.2 (hT.1 a)
    have hasym : ∀ y z, asymmPart (oplus R a b) y z ↔ asymmPart R y z ∨ (y = a ∧ z = b) := by
      intro y z
      simp only [asymmPart, oplus]
      simp only [asymmPart] at hRab hRba
      by_cases e1 : y = a <;> by_cases e2 : z = b <;> by_cases e3 : z = a <;> by_cases e4 : y = b <;>
        simp_all
    have hne : x ≠ b → (x ∈ maxSet S R ↔ x ∈ maxSet S (oplus R a b)) := by
      intro hxb
      rw [ps_mem_max, ps_mem_max]
      simp only [hasym]
      constructor
      · rintro ⟨hx, h⟩; refine ⟨hx, fun y hy hh => ?_⟩
        rcases hh with hh | hh
        · exact h y hy hh
        · exact hxb hh.2
      · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    have h01 : x ∈ maxSet S (oplus R a b) → x ∈ maxSet S R := by
      rw [ps_mem_max, ps_mem_max]; simp only [hasym]
      rintro ⟨hx, h⟩; exact ⟨hx, fun y hy hh => h y hy (Or.inl hh)⟩
    have h1T : x = b → x ∈ maxSet S R → x ∉ maxSet S (oplus R a b) → x ∉ maxSet S T := by
      rintro rfl hR h0 hTm
      rw [ps_mem_max] at hR hTm h0
      simp only [hasym] at h0
      apply h0
      refine ⟨hR.1, fun y hy hh => ?_⟩
      rcases hh with hh | ⟨rfl, -⟩
      · exact hR.2 y hy hh
      · exact hTm.2 y hy hTab
    by_cases hxb : x = b
    · have := h1T hxb; tauto
    · have := hne hxb; tauto

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (R R0 T : X → X → Prop) (hR : IsAcyclicOrder R) (hT : IsAcyclicOrder T)
    (h : OneStepToward R R0 T) (S : Finset X) :
    Disjoint (symmDiff (maxSet S R) (maxSet S R0)) (symmDiff (maxSet S R0) (maxSet S T)) ∧
      symmDiff (maxSet S R) (maxSet S R0) ∪ symmDiff (maxSet S R0) (maxSet S T) =
        symmDiff (maxSet S R) (maxSet S T) := by
  constructor
  · rw [Finset.disjoint_left]
    intro x h1 h2
    exact ps_key R R0 T hT h S x ⟨h1, h2⟩
  · ext x
    have := ps_key R R0 T hT h S x
    simp only [Finset.mem_union, Finset.mem_symmDiff] at this ⊢
    tauto
