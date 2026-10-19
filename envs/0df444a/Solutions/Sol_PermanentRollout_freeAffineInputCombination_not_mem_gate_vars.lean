-- Prove2me | solution 1 for PermanentRollout.freeAffineInputCombination_not_mem_gate_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/b4a3003a-9002-4e5e-b445-1dc810756421

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
    {k n : ℕ} (coefficients : Fin k →₀ ℂ) (i : Fin n) :
    Sum.inr i ∉
      (Finsupp.linearCombination ℂ
        (fun a : Fin k => MvPolynomial.X (Sum.inl a))
        coefficients : MvPolynomial (Fin k ⊕ Fin n) ℂ).vars := by
  classical
  intro hi
  simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hi
  have hsum := MvPolynomial.vars_sum_subset coefficients.support
    (fun r => coefficients r •
      (MvPolynomial.X (Sum.inl r) : MvPolynomial (Fin k ⊕ Fin n) ℂ)) hi
  rw [Finset.mem_biUnion] at hsum
  obtain ⟨r, _, hvar⟩ := hsum
  rw [MvPolynomial.smul_eq_C_mul] at hvar
  have hproduct := MvPolynomial.vars_mul
    (MvPolynomial.C (coefficients r))
    (MvPolynomial.X (Sum.inl r)) hvar
  simp at hproduct
end PermanentRollout
