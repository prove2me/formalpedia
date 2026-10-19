-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendReverseProducts_eval_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/68f1f718-3812-42fd-836e-b5bfff7913c0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values_getD_of_lt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length)
    (form : FreeAffineForm ι)
    (hform : ∀ index, form.gateCoefficients index ≠ 0 →
      index < circuit.program.length) :
    form.eval (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).values = form.eval circuit.values := by
  simp only [FreeAffineForm.eval]
  congr 1
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro index hindex
  rw [appendReverseProducts_values_getD_of_lt circuit adjoint
    left right hadjoint hleft hright index
      (hform index (Finsupp.mem_support_iff.mp hindex))]
end PermanentRollout.ReverseAdjoint
