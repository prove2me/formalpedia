-- Prove2me | solution 1 for Psi.stEast_UDpair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:57:20.609896+00:00
-- url     : https://prove2.me/submissions/ac4f47f2-5e82-4a0b-94a6-cf8925a0cdd7

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (x : Bool) : stEast [true, false] x = true := rfl
end Psi
