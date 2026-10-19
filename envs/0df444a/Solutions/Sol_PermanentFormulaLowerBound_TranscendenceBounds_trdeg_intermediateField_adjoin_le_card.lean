-- Prove2me | solution 1 for PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_adjoin_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/e04d6171-de15-453b-a664-10b6a2b06820

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.TranscendenceBounds
namespace PermanentFormulaLowerBound.TranscendenceBounds
theorem _root_.solution
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (s : Finset E) :
    Algebra.trdeg F (IntermediateField.adjoin F (s : Set E)) ≤
      (s.card : Cardinal) := by
  classical
  let K : IntermediateField F E := IntermediateField.adjoin F (s : Set E)
  let x : s → K := fun a =>
    ⟨a, IntermediateField.subset_adjoin F (s : Set E) a.property⟩
  have himage : Subtype.val '' Set.range x = (s : Set E) := by
    ext a
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact b.property
    · intro ha
      exact ⟨x ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have htop :
      IntermediateField.adjoin F (Set.range x) =
        (⊤ : IntermediateField F K) := by
    apply IntermediateField.lift_injective K
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, himage]
  have halgebraic :
      Algebra.IsAlgebraic (Algebra.adjoin F (Set.range x)) K := by
    apply IntermediateField.isAlgebraic_adjoin_iff_top.mp
    rw [htop]
    refine ⟨fun a => ?_⟩
    simpa using
      (isAlgebraic_algebraMap
        (R := (⊤ : IntermediateField F K)) (A := K)
        (⟨a, by simp⟩ : (⊤ : IntermediateField F K)))
  letI : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range x)) K :=
    halgebraic
  change Algebra.trdeg F K ≤ (s.card : Cardinal)
  calc
    Algebra.trdeg F K ≤ Cardinal.mk (Set.range x) :=
      Algebra.IsAlgebraic.trdeg_le_cardinalMk F (Set.range x)
    _ ≤ Cardinal.mk s := Cardinal.mk_range_le
    _ = (s.card : Cardinal) := Cardinal.mk_coe_finset
end PermanentFormulaLowerBound.TranscendenceBounds
