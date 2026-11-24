-- Prove2me | solution 2 for Psi.noDescent_cc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:42.802413+00:00
-- url     : https://prove2.me/submissions/4a7f9c47-9ecc-4735-8556-14c3d95e2a12

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (x y : Bool) (r : List Bool) :
    noDescent (x :: y :: r) = ((!x || y) && noDescent (y :: r)) := rfl
end Psi
