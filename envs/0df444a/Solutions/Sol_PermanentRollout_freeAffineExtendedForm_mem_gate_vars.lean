-- Prove2me | solution 1 for PermanentRollout.freeAffineExtendedForm_mem_gate_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/21ef6c53-9aa6-43ac-990c-3a0bdf818bfd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineGateCombination_mem_vars
import Theorems.Thm_PermanentRollout_freeAffineInputCombination_not_mem_gate_vars

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k n : ℕ} (form : FreeAffineForm (Fin k))
    (position : ℕ)
    (hposition : ∀ r ∈ form.gateCoefficients.support, r < position)
    (i : Fin n)
    (hi : Sum.inr i ∈
      (freeAffineExtendedForm (n := n) form).vars) :
    i.val < position := by
  classical
  unfold freeAffineExtendedForm at hi
  have houter := MvPolynomial.vars_add_subset
    (MvPolynomial.C form.constant +
      Finsupp.linearCombination ℂ
        (fun a : Fin k => MvPolynomial.X (Sum.inl a))
        form.inputCoefficients)
    (Finsupp.linearCombination ℂ
      (freeAffineGateReference (k := k) (n := n))
      form.gateCoefficients) hi
  rw [Finset.mem_union] at houter
  rcases houter with hconstantOrInput | hgate
  · have hinner := MvPolynomial.vars_add_subset
      (MvPolynomial.C form.constant)
      (Finsupp.linearCombination ℂ
        (fun a : Fin k => MvPolynomial.X (Sum.inl a))
        form.inputCoefficients) hconstantOrInput
    rw [Finset.mem_union, MvPolynomial.vars_C] at hinner
    have hinput : Sum.inr i ∈
        (Finsupp.linearCombination ℂ
          (fun a : Fin k => MvPolynomial.X (Sum.inl a))
          form.inputCoefficients :
            MvPolynomial (Fin k ⊕ Fin n) ℂ).vars := by
      simpa using hinner
    exact False.elim
      (freeAffineInputCombination_not_mem_gate_vars
        form.inputCoefficients i hinput)
  · obtain ⟨r, hr, heq⟩ :=
      freeAffineGateCombination_mem_vars
        form.gateCoefficients i hgate
    simpa [heq] using hposition r hr
end PermanentRollout
