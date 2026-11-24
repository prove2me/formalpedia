-- Prove2me | solution 1 for Psi.cc_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:32.418328+00:00
-- url     : https://prove2.me/submissions/44633b26-8fe8-4b4c-a8d1-5f2fd5ce7f54

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) : cc (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hstep : cc (List.replicate (m + 1) false) = false :: cc (List.replicate m false) := by
      cases m with
      | zero => rfl
      | succ p => rfl
    rw [hstep, ih, List.replicate_succ]
end Psi
