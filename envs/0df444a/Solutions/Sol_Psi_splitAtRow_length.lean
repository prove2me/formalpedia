-- Prove2me | solution 1 for Psi.splitAtRow_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:23.787971+00:00
-- url     : https://prove2.me/submissions/49fcfb5c-202a-4afe-a7c9-c55e29f258ee

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_splitAtRow_append

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.length + (splitAtRow p h).2.length = p.length := by
  have := splitAtRow_append p h
  have : ((splitAtRow p h).1 ++ (splitAtRow p h).2).length = p.length := by rw [this]
  simpa using this
end Psi
