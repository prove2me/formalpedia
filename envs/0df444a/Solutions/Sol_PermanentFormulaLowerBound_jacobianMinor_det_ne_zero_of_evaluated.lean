-- Prove2me | solution 1 for PermanentFormulaLowerBound.jacobianMinor_det_ne_zero_of_evaluated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/52040e26-f1ce-4300-bbc4-e1cf5b1aebae

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [CommRing F]
    [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ) (x : κ → F)
    (h : (evaluatedJacobianMinor g cols x).det ≠ 0) :
    (jacobianMinor g cols).det ≠ 0 := by
  intro hzero
  apply h
  change Matrix.det ((MvPolynomial.eval x).mapMatrix (jacobianMinor g cols)) = 0
  rw [← RingHom.map_det, hzero, map_zero]
end PermanentFormulaLowerBound
