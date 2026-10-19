-- Prove2me | solution 1 for PermanentFormulaLowerBound.algebraicIndependent_of_evaluatedJacobianMinor_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/15683ac4-3a02-405f-af34-2a0aeaca09b3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_jacobianMinor_det_ne_zero_of_evaluated
import Theorems.Thm_PermanentFormulaLowerBound_algebraicIndependent_of_jacobianMinor_det_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution
    [Field F] [CharZero F] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F)
    (hdet : (evaluatedJacobianMinor g cols x).det ≠ 0) :
    AlgebraicIndependent F g :=
  algebraicIndependent_of_jacobianMinor_det_ne_zero g cols
    (jacobianMinor_det_ne_zero_of_evaluated g cols x hdet)
end PermanentFormulaLowerBound
