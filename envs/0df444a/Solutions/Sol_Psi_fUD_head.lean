-- Prove2me | solution 1 for Psi.fUD_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:31:06.877412+00:00
-- url     : https://prove2.me/submissions/aa643704-1fee-4093-88c5-7153bdd9f44c

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m : Nat) : (fUD m).head? ≠ some false := by
  cases m with
  | zero => simp [fUD]
  | succ k => rw [fUD, List.replicate_succ, List.flatten_cons]; simp
end Psi
