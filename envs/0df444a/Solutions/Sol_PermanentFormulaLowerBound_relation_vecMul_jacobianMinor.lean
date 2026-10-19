-- Prove2me | solution 1 for PermanentFormulaLowerBound.relation_vecMul_jacobianMinor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/5299c340-a7b2-4d43-8522-0433ddb35ae9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_pderiv_aeval_chain_rule

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [CommRing F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (H : MvPolynomial ι F) (hH : MvPolynomial.aeval g H = 0) :
    (fun i : ι => MvPolynomial.aeval g (MvPolynomial.pderiv i H)) ᵥ*
        jacobianMinor g cols = 0 := by
  classical
  funext j
  have hj := congrArg (MvPolynomial.pderiv (cols j)) hH
  rw [pderiv_aeval_chain_rule] at hj
  simpa [Matrix.vecMul, dotProduct, jacobianMinor] using hj
end PermanentFormulaLowerBound
