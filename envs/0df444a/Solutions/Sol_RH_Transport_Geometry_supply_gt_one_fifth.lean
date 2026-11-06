-- Prove2me | solution 1 for RH.Transport.Geometry.supply_gt_one_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:29.03023+00:00
-- url     : https://prove2.me/submissions/b8625c57-df49-403d-9fb6-bca95c6eaa1c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_h_pos
import Theorems.Thm_RH_Transport_Geometry_supply_margin_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) :
    (1 / 5 : ℝ) < ell p / h p := by
  apply (lt_div_iff₀ (h_pos hp)).2
  have hm := supply_margin_pos hp
  linarith
end RH.Transport.Geometry
