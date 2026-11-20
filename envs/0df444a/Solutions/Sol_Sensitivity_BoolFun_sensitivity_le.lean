-- Prove2me | solution 1 for Sensitivity.BoolFun.sensitivity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:54:34.826558+00:00
-- url     : https://prove2.me/submissions/18ef7e37-63b3-486b-b249-0a47fcdcd0cf

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) : f.sensitivity ≤ n := by
  apply Finset.sup_le
  intro x _
  unfold localSensitivity
  calc (Finset.univ.filter fun i => f.sensitiveAt x i).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n
end BoolFun
end Sensitivity
