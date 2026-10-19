-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.foldl_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/d94b7af9-ddec-4840-9249-8bb68a625f3a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_step_potential

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (values : Array (MvPolynomial ι ℂ))
    (instructions : List (FreeAffineInstruction ι × ℕ))
    (state : ReverseAdjoint ι) (input : ι)
    (hgate : ∀ instruction ∈ instructions,
      values.getD instruction.2 0 = instruction.1.eval values) :
    (instructions.foldl (step values) state).potential values input =
      state.potential values input := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [List.foldl_cons, ih (step values state instruction)
      (fun gate hmem => hgate gate (by simp [hmem]))]
    exact step_potential values state instruction input
      (hgate instruction (by simp))
end PermanentRollout.ReverseAdjoint
