-- Prove2me | solution 1 for Psi.splitAtRow_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:50:59.742811+00:00
-- url     : https://prove2.me/submissions/1c211f11-5a6a-4bb9-8cd3-ef9bb0c34465

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 ++ (splitAtRow p h).2 = p := by
  fun_induction splitAtRow p h <;> simp_all
end Psi
