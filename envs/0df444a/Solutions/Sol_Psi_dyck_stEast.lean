-- Prove2me | solution 1 for Psi.dyck_stEast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:28:20.647138+00:00
-- url     : https://prove2.me/submissions/dde01a7f-453c-4751-80db-a96d319292b0

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_stEast_getLast_false
import Theorems.Thm_Psi_dyck_ends_east

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) :
    stEast p false = true := stEast_getLast_false p (dyck_ends_east p hd hne) false
end Psi
