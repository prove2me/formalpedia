-- Prove2me | solution 1 for Psi.drop_a_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:03:37.919915+00:00
-- url     : https://prove2.me/submissions/650ecdb4-f6e1-4f7e-aa53-cd4e0815fe9f

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (w' : List Bool) :
    (List.replicate a false ++ List.replicate b true ++ false :: w').drop a
      = List.replicate b true ++ false :: w' := by
  rw [List.append_assoc, List.drop_append_of_le_length (by simp),
    List.drop_eq_nil_of_le (by simp), List.nil_append]
end Psi
