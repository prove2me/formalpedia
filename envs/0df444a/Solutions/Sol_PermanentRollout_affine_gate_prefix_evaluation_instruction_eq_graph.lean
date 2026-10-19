-- Prove2me | solution 1 for PermanentRollout.affine_gate_prefix_evaluation_instruction_eq_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/8d5c12bc-5623-458d-950f-4dd6c620e59e

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
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (j : Fin q)
    (hprevious : ∀ i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (hgate : gate j = affineGateGraphEvaluation gate (rhs j)) :
    affineGatePrefixEvaluation gate j.val
        (MvPolynomial.X (Sum.inr j) - rhs j) =
      MvPolynomial.X (Sum.inr j) -
        MvPolynomial.rename Sum.inl (gate j) := by
  rw [map_sub,
    affine_gate_prefix_evaluation_eq_graph_of_previous
      gate j.val (rhs j) hprevious]
  have hX : affineGatePrefixEvaluation gate j.val
      (MvPolynomial.X (Sum.inr j)) =
        MvPolynomial.X (Sum.inr j) := by
    simp [affineGatePrefixEvaluation]
  rw [hX, ← hgate]
end PermanentRollout
