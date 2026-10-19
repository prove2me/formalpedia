-- Prove2me | solution 1 for PermanentRollout.affine_instruction_isSMulRegular_mod_prefix_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/f960b137-7eaa-4069-a432-e295af99e205

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_gate_prefix_graph_ideal_isPrime
import Theorems.Thm_PermanentRollout_affine_instruction_not_mem_prefix_graph

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
    IsSMulRegular
      (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
        affineGatePrefixGraphIdeal gate j.val)
      (MvPolynomial.X (Sum.inr j) - rhs j) := by
  let I := affineGatePrefixGraphIdeal gate j.val
  have hprime : I.IsPrime :=
    affine_gate_prefix_graph_ideal_isPrime gate j.val
  have hnot : MvPolynomial.X (Sum.inr j) - rhs j ∉ I :=
    affine_instruction_not_mem_prefix_graph
      gate rhs j hprevious hgate
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    I (MvPolynomial.X (Sum.inr j) - rhs j)).mpr
  intro p hp
  rw [smul_eq_mul] at hp
  exact (hprime.mem_or_mem hp).resolve_left hnot
end PermanentRollout
