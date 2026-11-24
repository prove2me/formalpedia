-- Prove2me | solution 1 for Psi.lead_true_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:02.750969+00:00
-- url     : https://prove2.me/submissions/a1c9b737-7279-415e-a26f-75f98f77f9f0

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_takeWhile_id_replicate

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (C : List Bool) :
    C = List.replicate ((C.takeWhile id).length) true ++ C.dropWhile id := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := id) (l := C), takeWhile_id_replicate]
end Psi
