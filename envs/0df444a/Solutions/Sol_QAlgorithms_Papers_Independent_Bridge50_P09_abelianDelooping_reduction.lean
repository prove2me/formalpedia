-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P09.abelianDelooping_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:26.829152+00:00
-- url     : https://prove2.me/submissions/b327ee8f-605e-4d33-a9ef-d19637599bc9

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P09

open scoped Manifold ContDiff
open QAlgorithms.Papers.Independent.Bridge50.P09

theorem s110_acs_bot {X A : Type*} [Group A] (alpha : X → A → A) (h : ∀ g a, alpha g a = a) :
    actionCommutatorSubgroup alpha = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le (⊥ : Subgroup A)).2
    rintro x ⟨g, a, rfl⟩
    simp [h]
  · exact bot_le

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : Type*) [CommGroup A] [TopologicalSpace A]
    [T2Space A] [SecondCountableTopology A] [ChartedSpace E A]
    [IsManifold (𝓘(ℝ, E)) ∞ A] [LieGroup (𝓘(ℝ, E)) ∞ A] :
    actionCommutatorSubgroup (trivialAction (A := A)) = ⊥ ∧
      ∃ e : (A ⧸ actionCommutatorSubgroup (trivialAction (A := A))) ≃* A,
        ∀ a : A, e (QuotientGroup.mk a) = a :=
  ⟨s110_acs_bot _ (fun _ _ => rfl),
    (QuotientGroup.quotientMulEquivOfEq (s110_acs_bot _ (fun _ _ => rfl))).trans QuotientGroup.quotientBot,
    fun _ => rfl⟩
