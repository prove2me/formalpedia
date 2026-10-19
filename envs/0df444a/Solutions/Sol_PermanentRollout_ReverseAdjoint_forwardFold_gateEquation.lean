-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.forwardFold_gateEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/be5f5a46-d90d-4c00-8c18-3197bf5d6501

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_getD_of_lt
import Theorems.Thm_PermanentRollout_ReverseAdjoint_eval_congr_of_referencesBounded

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ))
    (hvalid : ∀ position : Fin program.length,
      (program.get position).referencesBounded
        (values.size + position.val))
    (position : Fin program.length) :
    (program.foldl forwardStep values).getD
        (values.size + position.val) 0 =
      (program.get position).eval
        (program.foldl forwardStep values) := by
  induction program generalizing values with
  | nil => exact Fin.elim0 position
  | cons instruction rest ih =>
    cases position using Fin.cases with
    | zero =>
      have hhead : instruction.referencesBounded values.size := by
        simpa using hvalid 0
      calc
        ((instruction :: rest).foldl forwardStep values).getD
            (values.size + (0 : Fin (instruction :: rest).length).val) 0 =
          (forwardStep values instruction).getD values.size 0 := by
            simp only [List.foldl_cons, Fin.val_zero, Nat.add_zero]
            apply forwardFold_getD_of_lt
            simp [forwardStep]
        _ = instruction.eval values := by
          simp [forwardStep, Array.getD_eq_getD_getElem?]
        _ = instruction.eval
              ((instruction :: rest).foldl forwardStep values) := by
          apply eval_congr_of_referencesBounded
            instruction values.size values _ hhead
          intro index hindex
          exact (forwardFold_getD_of_lt
            (instruction :: rest) values index hindex).symm
        _ = ((instruction :: rest).get
              (0 : Fin (instruction :: rest).length)).eval
              ((instruction :: rest).foldl forwardStep values) := rfl
    | succ position =>
      let next := forwardStep values instruction
      have hrest : ∀ index : Fin rest.length,
          (rest.get index).referencesBounded
            (next.size + index.val) := by
        intro index
        have hindex := hvalid index.succ
        simpa [next, forwardStep, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hindex
      have htail := ih next hrest position
      simpa [next, List.foldl_cons, forwardStep, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using htail
end PermanentRollout.ReverseAdjoint
