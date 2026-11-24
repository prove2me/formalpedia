-- Prove2me | solution 2 for Psi.cLead0_block
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T23:47:58.209794+00:00
-- url     : https://prove2.me/submissions/96aa7116-2612-4fdf-a288-6e7a81a05c92

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi


theorem solution (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    cLead0 (List.replicate a false ++ List.replicate b true ++ false :: w') = a := by
  cases b with
  | zero => omega
  | succ k =>
    induction a with
    | zero => simp [List.replicate_succ, cLead0]
    | succ a ih => rw [List.replicate_succ, List.cons_append, List.cons_append]; change 1 + cLead0 _ = _; rw [ih]; omega
