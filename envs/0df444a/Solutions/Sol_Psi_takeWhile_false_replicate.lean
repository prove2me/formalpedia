-- Prove2me | solution 1 for Psi.takeWhile_false_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:40.738873+00:00
-- url     : https://prove2.me/submissions/722cc94b-b4a1-4fe9-bcba-bd951c3fb523

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (xs : List Bool) :
    xs.takeWhile (· = false) = List.replicate (xs.takeWhile (· = false)).length false := by
  induction xs with
  | nil => simp
  | cons a t ih => cases a with
    | true => simp
    | false => rw [show (false :: t).takeWhile (· = false) = false :: t.takeWhile (· = false) from rfl,
                  List.length_cons, List.replicate_succ, ← ih]
end Psi
