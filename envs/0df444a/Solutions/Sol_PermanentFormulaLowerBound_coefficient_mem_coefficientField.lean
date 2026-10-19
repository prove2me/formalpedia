-- Prove2me | solution 1 for PermanentFormulaLowerBound.coefficient_mem_coefficientField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/4d2c3cf6-4b40-4799-bfa7-72a4d2d5e43b

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {Y : Type u} {Z : Type v} {F : Type w} [Field F]
namespace PermanentFormulaLowerBound
theorem _root_.solution
    (f : MvPolynomial (Y ⊕ Z) F) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (coefficientPolynomial f α) ∈ coefficientField f := by
  unfold coefficientField
  exact IntermediateField.subset_adjoin F _ ⟨α, rfl⟩
end PermanentFormulaLowerBound
