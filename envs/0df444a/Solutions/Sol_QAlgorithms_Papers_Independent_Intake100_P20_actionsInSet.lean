-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.actionsInSet
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:24:17.102209+00:00
-- url     : https://prove2.me/submissions/2657873e-8f10-47ec-98c2-5d627febb30f

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF pp. 4–5: diagrammatic actions in Set are ordinary left actions,
preserving the given map. As the source observes, this includes monoids.
The type X is allowed to be empty. -/
theorem solution {M : Type u} [Monoid M] {X : Type v} (n : M × X → X) :
    ActionDiagrams n ↔
      ∃ a : MulAction M X, ∀ g x, @SMul.smul M X a.toSMul g x = n (g, x) := by
  constructor
  · intro h
    exact ⟨actionOfMap n h,fun _ _ => rfl⟩
  · rintro ⟨a,ha⟩
    letI : MulAction M X := a
    constructor
    · intro x
      rw [← ha]; exact a.one_smul x
    · intro g k x
      simp_rw [← ha]; exact a.mul_smul g k x
