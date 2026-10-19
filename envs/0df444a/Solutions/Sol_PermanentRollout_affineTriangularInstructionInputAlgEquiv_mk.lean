-- Prove2me | solution 1 for PermanentRollout.affineTriangularInstructionInputAlgEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/9ba1d763-32a2-4af8-a50a-f7dcb0a93f22

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (p : MvPolynomial (Fin k ⊕ Fin q) ℂ) :
    affineTriangularInstructionInputAlgEquiv rhs gate hgate htop
      (Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs) p) =
        affineGateGraphEvaluation gate p := by
  rw [affineTriangularInstructionInputAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl
end PermanentRollout
