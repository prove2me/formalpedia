-- Prove2me | solution 1 for Psi.cLead1_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:25:22.940961+00:00
-- url     : https://prove2.me/submissions/828c0c85-6ffb-4323-bd2a-b24cc4251da6

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) : (w.drop (cLead1 w)).head? ≠ some true := by
  fun_induction cLead1 w with
  | case1 r ih =>
      rw [show 1 + cLead1 r = cLead1 r + 1 from by omega, List.drop_succ_cons]; exact ih
  | case2 t h =>
      cases t with
      | nil => simp
      | cons a t' => cases a with
        | true => exact (h t' rfl).elim
        | false => simp
end Psi
