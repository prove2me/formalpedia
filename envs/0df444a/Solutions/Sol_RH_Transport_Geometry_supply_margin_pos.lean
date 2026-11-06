-- Prove2me | solution 1 for RH.Transport.Geometry.supply_margin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:55.6872+00:00
-- url     : https://prove2.me/submissions/4b66b506-ef1a-4bec-9b6f-6ce490aea1e9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
import Theorems.Thm_RH_Transport_Geometry_supply_margin_identity

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) :
    0 < 5 * ell p - h p := by
  rw [supply_margin_identity]
  linarith
end RH.Transport.Geometry
