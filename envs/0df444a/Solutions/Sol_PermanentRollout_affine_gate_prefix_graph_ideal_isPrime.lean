-- Prove2me | solution 1 for PermanentRollout.affine_gate_prefix_graph_ideal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/464807d0-1203-4d84-b943-369e40d81856

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
theorem _root_.solution {k q : ℕ}
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (n : ℕ) :
    (affineGatePrefixGraphIdeal gate n).IsPrime := by
  rw [affine_gate_prefix_graph_ideal_eq_ker gate n]
  exact RingHom.ker_isPrime
    (affineGatePrefixEvaluation gate n).toRingHom
end PermanentRollout
