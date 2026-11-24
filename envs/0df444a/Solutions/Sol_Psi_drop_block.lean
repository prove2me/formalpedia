-- Prove2me | solution 1 for Psi.drop_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:16:54.490943+00:00
-- url     : https://prove2.me/submissions/c7a3b6b7-a0d8-4786-b596-5e565081ac42

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (b : ℕ) (w' : List Bool) :
    (List.replicate b true ++ false :: w').drop (b + 1) = w' := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append, List.length_replicate,
    show b + 1 - b = 1 from by omega]; rfl
end Psi
