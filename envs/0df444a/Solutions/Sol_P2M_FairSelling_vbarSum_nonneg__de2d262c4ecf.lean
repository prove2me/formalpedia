-- Prove2me | solution 1 for P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:18:26.33861+00:00
-- url     : https://prove2.me/submissions/827b659d-0b47-4ed6-b6a7-f5b63c5706b7

import Mathlib
import Definitions.Def_RequestProject_Selling
open FairSelling
variable {G : Type*}


theorem solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (Y : Finset G) :
    0 ≤ vbarSum w p Y := by
  exact Finset.sum_nonneg fun g _ => (hw g).trans (le_max_right _ _)
