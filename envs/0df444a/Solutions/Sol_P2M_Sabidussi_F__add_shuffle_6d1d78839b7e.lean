-- Prove2me | solution 1 for P2M_Sabidussi_F__add_shuffle_6d1d78839b7e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:19.824737+00:00
-- url     : https://prove2.me/submissions/16fb933e-69f0-4314-bc80-c8507cd5abdd

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (a b : F₂) : a + (b + (a + b)) = 0 := by
  calc
    a + (b + (a + b)) = (a + a) + (b + b) := by abel
    _ = 0 := by simp
end Sabidussi
