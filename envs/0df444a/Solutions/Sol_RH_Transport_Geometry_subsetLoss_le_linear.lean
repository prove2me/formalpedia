-- Prove2me | solution 1 for RH.Transport.Geometry.subsetLoss_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:55:51.936261+00:00
-- url     : https://prove2.me/submissions/7c8db55d-a883-4061-a0c7-3de47f6cabce

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_positive_part_le_subset

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    subsetLoss p d ≤ -(7 / 8 : ℝ) * d := by
  have hm := positive_part_le_subset hp hd
  dsimp [subsetLoss]
  linarith
end RH.Transport.Geometry
