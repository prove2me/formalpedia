-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.step_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/c3b3532c-e504-4dcf-a1f8-bde4a0acc95c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_potential_affine
import Theorems.Thm_PermanentRollout_ReverseAdjoint_potential_mul

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
    (state : ReverseAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ) (input : ι)
    (hgate : values.getD instruction.2 0 =
      instruction.1.eval values) :
    (step values state instruction).potential values input =
      state.potential values input := by
  cases instruction with
  | mk instruction position =>
    cases instruction with
    | affine form =>
      exact potential_affine state values position form input hgate
    | mul left right =>
      exact potential_mul state values position left right input hgate
end PermanentRollout.ReverseAdjoint
