-- Prove2me | solution 1 for Psi.cLead0_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:27.266438+00:00
-- url     : https://prove2.me/submissions/c89d04e9-134a-4355-a445-52996fed5324

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) :
    w.take (cLead0 w) = List.replicate (cLead0 w) false := by
  fun_induction cLead0 w with
  | case1 r ih =>
      rw [show 1 + cLead0 r = cLead0 r + 1 from by omega, List.take_succ_cons,
        List.replicate_succ, ih]
  | case2 t h => simp
end Psi
