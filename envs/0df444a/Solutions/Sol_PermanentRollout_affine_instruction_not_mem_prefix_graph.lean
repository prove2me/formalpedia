-- Prove2me | solution 1 for PermanentRollout.affine_instruction_not_mem_prefix_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/fb59d09c-1c56-4773-a969-83b95dc5c7e4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_gate_graph_equation_ne_zero
import Theorems.Thm_PermanentRollout_affine_gate_prefix_evaluation_instruction_eq_graph

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
    MvPolynomial.X (Sum.inr j) - rhs j ∉
      affineGatePrefixGraphIdeal gate j.val := by
  intro hmem
  rw [affine_gate_prefix_graph_ideal_eq_ker] at hmem
  change affineGatePrefixEvaluation gate j.val
    (MvPolynomial.X (Sum.inr j) - rhs j) = 0 at hmem
  rw [affine_gate_prefix_evaluation_instruction_eq_graph
    gate rhs j hprevious hgate] at hmem
  exact affine_gate_graph_equation_ne_zero gate j hmem
end PermanentRollout
