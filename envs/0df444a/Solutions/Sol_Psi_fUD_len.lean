-- Prove2me | solution 1 for Psi.fUD_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:03:11.848803+00:00
-- url     : https://prove2.me/submissions/94b66871-2bab-46b7-b691-cac226bcaa6d

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) : (List.replicate n [true, false]).flatten.length = 2 * n := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; ring
end Psi
