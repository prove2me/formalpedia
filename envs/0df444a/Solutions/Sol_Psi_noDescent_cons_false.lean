-- Prove2me | solution 1 for Psi.noDescent_cons_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:07:45.793741+00:00
-- url     : https://prove2.me/submissions/62e3caba-9645-4338-8fab-4f8720b701d3

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) :
    noDescent (false :: rest) = noDescent rest := by
  cases rest with | nil => simp [noDescent] | cons y ys => simp [noDescent]
end Psi
