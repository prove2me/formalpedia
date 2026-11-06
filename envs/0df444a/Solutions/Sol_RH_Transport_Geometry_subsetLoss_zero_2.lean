-- Prove2me | solution 2 for RH.Transport.Geometry.subsetLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:20.0267+00:00
-- url     : https://prove2.me/submissions/d62b3ace-b2a1-4a33-bddd-c17747c99a05

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_ell_lt_one_fifth

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : p < 1 / 30) :
    subsetLoss p 0 = 0 := by
  have he := ell_lt_one_fifth hp
  have hn : 5 * ell p - 1 + 0 ≤ 0 := by linarith
  dsimp [subsetLoss]
  rw [max_eq_left hn]
  ring
end RH.Transport.Geometry
