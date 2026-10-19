-- Prove2me | solution 1 for PermanentRollout.affineTriangularInstructionOutputClosedFiber_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/becd8441-a3b0-4fc2-8577-66f30732201b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_closedFiber_finrank

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
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i) :
    Module.finrank ℂ
      (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
        (affineTriangularInstructionIdeal rhs ⊔
          affineGateRawOutputIdeal output target)) = e ^ k := by
  let E := affineTriangularInstructionOutputClosedFiberAlgEquiv
    rhs gate output F target hgate htop houtput
  exact E.toLinearEquiv.finrank_eq.trans
    (homogeneousMap_closedFiber_finrank k F e he hF hzero target)
end PermanentRollout
