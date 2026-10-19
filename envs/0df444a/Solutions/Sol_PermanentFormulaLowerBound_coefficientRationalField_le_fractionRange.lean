-- Prove2me | solution 1 for PermanentFormulaLowerBound.coefficientRationalField_le_fractionRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/6901924f-d8a0-4be6-b70f-a90aa11f1885

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
noncomputable section
variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]
namespace PermanentFormulaLowerBound
theorem _root_.solution (s : Finset E) :
    coefficientRationalField (F := F) (Y := Y) s ≤
      (coefficientFractionEmbedding (Y := Y)
        (IntermediateField.adjoin F (s : Set E))).fieldRange := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases hx with ⟨i, rfl⟩ | ⟨c, hc, rfl⟩
  · apply AlgHom.mem_fieldRange.mpr
    refine ⟨algebraMap
      (MvPolynomial Y (IntermediateField.adjoin F (s : Set E)))
      (FractionRing (MvPolynomial Y
        (IntermediateField.adjoin F (s : Set E))))
      (MvPolynomial.X i), ?_⟩
    rw [coefficientFractionEmbedding_algebraMap]
    simp [coefficientPolynomialEmbedding]
  · let ck : IntermediateField.adjoin F (s : Set E) :=
      ⟨c, IntermediateField.subset_adjoin F (s : Set E) hc⟩
    apply AlgHom.mem_fieldRange.mpr
    refine ⟨algebraMap
      (MvPolynomial Y (IntermediateField.adjoin F (s : Set E)))
      (FractionRing (MvPolynomial Y
        (IntermediateField.adjoin F (s : Set E))))
      (MvPolynomial.C ck), ?_⟩
    rw [coefficientFractionEmbedding_algebraMap]
    simpa [coefficientPolynomialEmbedding, ck] using
      (IsScalarTower.algebraMap_apply E (MvPolynomial Y E)
        (FractionRing (MvPolynomial Y E)) c).symm
end PermanentFormulaLowerBound
