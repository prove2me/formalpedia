-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.forwardFold_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/70a0cc91-97b2-4b7e-a71b-34a6a5161257

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.CircuitPrefix
namespace PermanentRollout.CircuitPrefix
theorem _root_.solution {ι : Type} (program : List (Instruction ι))
    (previous : Array (MvPolynomial ι ℂ)) :
    (program.foldl
      (fun values instruction => values.push (instruction.eval values))
        previous).size = previous.size + program.length := by
  induction program generalizing previous with
  | nil => simp
  | cons instruction rest ih =>
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      ih (previous.push (instruction.eval previous))
end PermanentRollout.CircuitPrefix
