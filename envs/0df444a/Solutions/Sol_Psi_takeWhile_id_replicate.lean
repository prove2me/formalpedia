-- Prove2me | solution 1 for Psi.takeWhile_id_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:18.645805+00:00
-- url     : https://prove2.me/submissions/cb8ec640-1b08-4e8e-ba1d-1d8d56fa20cd

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (xs : List Bool) :
    xs.takeWhile id = List.replicate (xs.takeWhile id).length true := by
  induction xs with
  | nil => simp
  | cons a t ih => cases a with
    | false => simp
    | true => rw [show (true :: t).takeWhile id = true :: t.takeWhile id from rfl,
                  List.length_cons, List.replicate_succ, ← ih]
end Psi
