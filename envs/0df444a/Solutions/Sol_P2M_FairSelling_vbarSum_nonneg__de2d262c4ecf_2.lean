-- Prove2me | solution 2 for P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:25.594513+00:00
-- url     : https://prove2.me/submissions/d26ec409-a77c-4439-b2bf-60eb3be9ba36

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (Y : Finset G) :
    0 ≤ vbarSum w p Y :=
  Finset.sum_nonneg (fun g _ => le_trans (hw g) (le_max_right _ _))
end FairSelling
