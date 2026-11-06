-- Prove2me | solution 1 for RH.Transport.Geometry.h_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:55:34.689721+00:00
-- url     : https://prove2.me/submissions/cbfe78df-1aa1-43a9-9c9f-596d199b3cf5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) : 0 < h p := by
  dsimp [h]
  linarith
end RH.Transport.Geometry
