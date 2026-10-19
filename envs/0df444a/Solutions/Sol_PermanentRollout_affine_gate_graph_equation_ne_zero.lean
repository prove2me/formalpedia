-- Prove2me | solution 1 for PermanentRollout.affine_gate_graph_equation_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/3573fc5a-9c5c-4a6e-897b-abb67aa5b35c

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
    (gate : Fin q → MvPolynomial (Fin k) ℂ) (j : Fin q) :
    MvPolynomial.X (Sum.inr j) -
      MvPolynomial.rename Sum.inl (gate j) ≠ 0 := by
  intro h
  have heq : (MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Fin k ⊕ Fin q) ℂ) =
      MvPolynomial.rename Sum.inl (gate j) := sub_eq_zero.mp h
  have hvar : Sum.inr j ∈
      (MvPolynomial.rename Sum.inl (gate j)).vars := by
    rw [← heq]
    simp
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename
    Sum.inl (gate j) hvar
  cases hi
end PermanentRollout
