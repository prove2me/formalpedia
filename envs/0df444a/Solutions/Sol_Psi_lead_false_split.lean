-- Prove2me | solution 1 for Psi.lead_false_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:14.765998+00:00
-- url     : https://prove2.me/submissions/d9489f46-6b3b-4511-a1a7-958a5b67e1dd

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_takeWhile_false_replicate

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (B : List Bool) :
    B = List.replicate ((B.takeWhile (· = false)).length) false ++ B.dropWhile (· = false) := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := (· = false)) (l := B),
    takeWhile_false_replicate]
end Psi
