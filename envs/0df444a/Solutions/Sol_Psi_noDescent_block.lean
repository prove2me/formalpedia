-- Prove2me | solution 1 for Psi.noDescent_block
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:47:59.678824+00:00
-- url     : https://prove2.me/submissions/b3846fe5-19ca-40ba-83d0-e627bd4f39df

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    noDescent (List.replicate a false ++ List.replicate b true ++ false :: w') = false := by
  have aux (s t : List Bool) : noDescent (s ++ true :: false :: t) = false := by
    induction s with
    | nil => simp [noDescent]
    | cons a s ih =>
      cases s with
      | nil => cases a <;> simp [noDescent]
      | cons b s => change ((!a || b) && noDescent ((b :: s) ++ true :: false :: t)) = false; rw [ih, Bool.and_false]
  cases b with
  | zero => omega
  | succ b => rw [List.replicate_succ']; simpa [List.append_assoc] using aux (List.replicate a false ++ List.replicate b true) w'
