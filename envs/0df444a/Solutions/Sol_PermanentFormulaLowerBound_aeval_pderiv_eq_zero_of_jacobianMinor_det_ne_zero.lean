-- Prove2me | solution 1 for PermanentFormulaLowerBound.aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/9c734b4f-02ad-451f-b910-8a2570faa289

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_relation_vecMul_jacobianMinor

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [Field F]
    [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (H : MvPolynomial ι F)
    (hdet : (jacobianMinor g cols).det ≠ 0)
    (hH : MvPolynomial.aeval g H = 0) (i : ι) :
    MvPolynomial.aeval g (MvPolynomial.pderiv i H) = 0 := by
  have hzero := Matrix.eq_zero_of_vecMul_eq_zero hdet
    (relation_vecMul_jacobianMinor g cols H hH)
  exact congrFun hzero i
end PermanentFormulaLowerBound
