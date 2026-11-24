-- Prove2me | solution 1 for P2M_FongoSync_lt_asymm__20b31d083484
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:00.623542+00:00
-- url     : https://prove2.me/submissions/635aaf5f-5fcb-49f3-bf34-927797deccfe

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution {x y : K} (h : cmp x y = .lt) : cmp y x ≠ .lt := by
  intro h'; have := OrientedCmp.gt_of_lt h; simp_all
end FongoSync
