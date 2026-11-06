-- Prove2me | solution 2 for RH.Transport.Geometry.supply_gt_inverse_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:19.277557+00:00
-- url     : https://prove2.me/submissions/167e4464-4cbd-4480-a8fe-975196e4991a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_supply_gt_one_fifth

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) :
    (7 / 37 : ℝ) < ell p / h p := by
  have hs := supply_gt_one_fifth hp
  linarith
end RH.Transport.Geometry
