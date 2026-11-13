-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kification_functorial
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T22:54:51.295534+00:00
-- url     : https://prove2.me/submissions/0e541511-fe80-4be6-ad9a-42a578c7dc5f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- The unnumbered k-functor assertion after B.4, PDF p. 36: continuity,
identity-on-points, and the identity and composition laws for the concrete lift. -/
theorem solution
    (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    Continuous (kMap f) ∧
    (∀ x : KSpace X, kMap f x = f x) ∧
    kMap (ContinuousMap.id X) = ContinuousMap.id (KSpace X) ∧
    kMap (g.comp f) = (kMap g).comp (kMap f) := by
  refine ⟨(kMap f).continuous, (fun x => rfl), ?_, ?_⟩ <;> ext x <;> rfl
