-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.actionsInTop
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:25:44.498197+00:00
-- url     : https://prove2.me/submissions/8886be2e-dbb8-4bf1-bf86-4855bc9b53c2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 5: actions in Top are jointly continuous ordinary actions.
There is no separation, compactness, or nonemptiness hypothesis on X. -/
theorem solution {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {X : Type v} [TopologicalSpace X] (n : G × X → X) :
    (ActionDiagrams n ∧ Continuous n) ↔
      ∃ a : MulAction G X,
        (∀ g x, @SMul.smul G X a.toSMul g x = n (g, x)) ∧
        (letI : MulAction G X := a; ContinuousSMul G X) := by
  constructor
  · rintro ⟨h,hc⟩
    letI : MulAction G X := actionOfMap n h
    refine ⟨actionOfMap n h,fun _ _ => rfl,?_⟩
    exact ⟨hc⟩
  · rintro ⟨a,ha,hc⟩
    letI : MulAction G X := a
    letI : ContinuousSMul G X := hc
    refine ⟨?_,?_⟩
    · constructor
      · intro x
        rw [← ha]; exact a.one_smul x
      · intro g k x
        simp_rw [← ha]; exact a.mul_smul g k x
    · have he : (fun p : G × X => p.1 • p.2) = n := funext (fun p => ha p.1 p.2)
      rw [← he]
      exact continuous_smul
