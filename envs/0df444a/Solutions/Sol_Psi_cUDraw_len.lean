-- Prove2me | solution 1 for Psi.cUDraw_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:34.530325+00:00
-- url     : https://prove2.me/submissions/0e84cc95-810b-4983-9224-e60c6929ade8

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_cUDraw_prefix

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (π : List Bool) : 2 * cUDraw π ≤ π.length := by
  conv_rhs => rw [cUDraw_prefix π]
  rw [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate]; simp; omega
end Psi
