-- Prove2me | solution 1 for Psi.cLead0_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:25:01.013066+00:00
-- url     : https://prove2.me/submissions/f57ab699-2ca8-4193-9084-3c39fe597592

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) : (w.drop (cLead0 w)).head? ≠ some false := by
  fun_induction cLead0 w with
  | case1 r ih =>
      rw [show 1 + cLead0 r = cLead0 r + 1 from by omega, List.drop_succ_cons]; exact ih
  | case2 t h =>
      cases t with
      | nil => simp
      | cons a t' => cases a with
        | false => exact (h t' rfl).elim
        | true => simp
end Psi
