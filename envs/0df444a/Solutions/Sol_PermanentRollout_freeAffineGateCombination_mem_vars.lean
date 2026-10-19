-- Prove2me | solution 1 for PermanentRollout.freeAffineGateCombination_mem_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/4138d19a-3a5c-484d-94a7-7677da9bec92

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineGateReference_mem_vars

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k n : ℕ} (coefficients : ℕ →₀ ℂ) (i : Fin n)
    (hi : Sum.inr i ∈
      (Finsupp.linearCombination ℂ
        (freeAffineGateReference (k := k) (n := n))
        coefficients).vars) :
    ∃ r ∈ coefficients.support, i.val = r := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hi
  have hsum := MvPolynomial.vars_sum_subset coefficients.support
    (fun r => coefficients r •
      freeAffineGateReference (k := k) (n := n) r) hi
  rw [Finset.mem_biUnion] at hsum
  obtain ⟨r, hr, hvar⟩ := hsum
  rw [MvPolynomial.smul_eq_C_mul] at hvar
  have hproduct := MvPolynomial.vars_mul
    (MvPolynomial.C (coefficients r))
    (freeAffineGateReference (k := k) (n := n) r) hvar
  rw [Finset.mem_union, MvPolynomial.vars_C] at hproduct
  have href : Sum.inr i ∈
      (freeAffineGateReference (k := k) (n := n) r).vars := by
    simpa using hproduct
  exact ⟨r, hr, freeAffineGateReference_mem_vars r i href⟩
end PermanentRollout
