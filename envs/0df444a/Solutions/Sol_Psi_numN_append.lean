-- Prove2me | solution 1 for Psi.numN_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:55:21.020534+00:00
-- url     : https://prove2.me/submissions/f092569d-0881-4df0-abf4-54f8454ebe19

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) : numN (p ++ q) = numN p + numN q := by
  unfold numN; rw [List.filter_append, List.length_append]
end Psi
