-- Prove2me | solution 1 for Psi.desComp_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:36:09.167066+00:00
-- url     : https://prove2.me/submissions/3de16a26-933f-4d3e-9d6f-66083396496a

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desCompAux_ne_nil

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (word : List Bool) : desComp word ≠ [] := desCompAux_ne_nil word 0
end Psi
