-- Prove2me | solution 1 for SingleMachinePrec.ConvexBipartite.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:32:22.264226+00:00
-- url     : https://prove2.me/submissions/37db571c-0b95-4f10-822d-47c1b708ea8d

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_IncPartition

set_option autoImplicit false
open SingleMachinePrec.ConvexBipartite
open ConvexBipartiteOrder

theorem solution {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ((∀ x y : Job a b, SingleMachinePrec.Framework.Incomparable C.prec x y ↔ (C.E1 x y ∨ C.E2 x y ∨ C.E3 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E1 x y ∧ C.E2 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E1 x y ∧ C.E3 x y)) ∧
      (∀ x y : Job a b, ¬ (C.E2 x y ∧ C.E3 x y))) ∧
    (∀ x y : Job a b, SingleMachinePrec.Framework.Incomparable C.prec x y →
      (C.E1 x y → ¬ C.E1 y x) ∧ (C.E2 x y → ¬ C.E2 y x) ∧ (C.E3 x y → ¬ C.E3 y x)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      simp [ConvexBipartiteOrder.E1, ConvexBipartiteOrder.E2, ConvexBipartiteOrder.E3,
        SingleMachinePrec.Framework.Incomparable, ConvexBipartiteOrder.prec]
    all_goals first
      | omega
      | (intro _ k hk h1 h2 _; exact ⟨k, hk, h1, h2⟩)
      | (by_cases hQ : ∃ k, i < k ∧ C.l k ≤ j ∧ j ≤ C.r k
         · have hQ2 : ¬ ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro hall; obtain ⟨k, hk, h1, h2⟩ := hQ; exact absurd (hall k hk h1) (not_lt.mpr h2)
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX
         · have hQ2 : ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro k hk h1; by_contra h; exact hQ ⟨k, hk, h1, not_lt.mp h⟩
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX)
  · intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      simp [ConvexBipartiteOrder.E1, ConvexBipartiteOrder.E2, ConvexBipartiteOrder.E3,
        SingleMachinePrec.Framework.Incomparable, ConvexBipartiteOrder.prec]
    all_goals first
      | omega
      | (intro _ k hk h1 h2 _; exact ⟨k, hk, h1, h2⟩)
      | (by_cases hQ : ∃ k, i < k ∧ C.l k ≤ j ∧ j ≤ C.r k
         · have hQ2 : ¬ ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro hall; obtain ⟨k, hk, h1, h2⟩ := hQ; exact absurd (hall k hk h1) (not_lt.mpr h2)
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX
         · have hQ2 : ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro k hk h1; by_contra h; exact hQ ⟨k, hk, h1, not_lt.mp h⟩
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX)
  · intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      simp [ConvexBipartiteOrder.E1, ConvexBipartiteOrder.E2, ConvexBipartiteOrder.E3,
        SingleMachinePrec.Framework.Incomparable, ConvexBipartiteOrder.prec]
    all_goals first
      | omega
      | (intro _ k hk h1 h2 _; exact ⟨k, hk, h1, h2⟩)
      | (by_cases hQ : ∃ k, i < k ∧ C.l k ≤ j ∧ j ≤ C.r k
         · have hQ2 : ¬ ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro hall; obtain ⟨k, hk, h1, h2⟩ := hQ; exact absurd (hall k hk h1) (not_lt.mpr h2)
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX
         · have hQ2 : ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro k hk h1; by_contra h; exact hQ ⟨k, hk, h1, not_lt.mp h⟩
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX)
  · intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      simp [ConvexBipartiteOrder.E1, ConvexBipartiteOrder.E2, ConvexBipartiteOrder.E3,
        SingleMachinePrec.Framework.Incomparable, ConvexBipartiteOrder.prec]
    all_goals first
      | omega
      | (intro _ k hk h1 h2 _; exact ⟨k, hk, h1, h2⟩)
      | (by_cases hQ : ∃ k, i < k ∧ C.l k ≤ j ∧ j ≤ C.r k
         · have hQ2 : ¬ ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro hall; obtain ⟨k, hk, h1, h2⟩ := hQ; exact absurd (hall k hk h1) (not_lt.mpr h2)
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX
         · have hQ2 : ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro k hk h1; by_contra h; exact hQ ⟨k, hk, h1, not_lt.mp h⟩
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX)
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;>
      simp [ConvexBipartiteOrder.E1, ConvexBipartiteOrder.E2, ConvexBipartiteOrder.E3,
        SingleMachinePrec.Framework.Incomparable, ConvexBipartiteOrder.prec]
    all_goals first
      | omega
      | (intro _ k hk h1 h2 _; exact ⟨k, hk, h1, h2⟩)
      | (by_cases hQ : ∃ k, i < k ∧ C.l k ≤ j ∧ j ≤ C.r k
         · have hQ2 : ¬ ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro hall; obtain ⟨k, hk, h1, h2⟩ := hQ; exact absurd (hall k hk h1) (not_lt.mpr h2)
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX
         · have hQ2 : ∀ (k : Fin b), i < k → C.l k ≤ j → C.r k < j := by
             intro k hk h1; by_contra h; exact hQ ⟨k, hk, h1, not_lt.mp h⟩
           constructor
           · intro hX; first | exact Or.inl ⟨hX, hQ⟩ | exact Or.inr ⟨hX, hQ2⟩
           · rintro (⟨hX, _⟩ | ⟨hX, _⟩) <;> exact hX)
