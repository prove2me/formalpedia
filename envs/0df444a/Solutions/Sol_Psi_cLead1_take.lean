-- Prove2me | solution 1 for Psi.cLead1_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:58.154231+00:00
-- url     : https://prove2.me/submissions/4639c94c-896d-4edc-9b45-1281ce4b92ec

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) :
    w.take (cLead1 w) = List.replicate (cLead1 w) true := by
  fun_induction cLead1 w with
  | case1 r ih =>
      rw [show 1 + cLead1 r = cLead1 r + 1 from by omega, List.take_succ_cons,
        List.replicate_succ, ih]
  | case2 t h => simp
end Psi
