-- Prove2me | solution 1 for Psi.numN_flatten_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:21.446506+00:00
-- url     : https://prove2.me/submissions/c1139bc2-9be2-4877-a421-5ea99721c801

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_numN_fUD

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : Nat) :
    numN ((List.replicate l [true, false]).flatten) = l := numN_fUD l
end Psi
