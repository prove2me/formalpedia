-- Prove2me | solution 2 for RH.Transport.Geometry.boundary_gt_thirteen_fifteenths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:52.253447+00:00
-- url     : https://prove2.me/submissions/a753d924-c4ef-4364-aa64-7110232752f6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ}
    (hp : p < 1 / 30) : (13 / 15 : ℝ) < boundary p := by
  dsimp [boundary]
  linarith
end RH.Transport.Geometry
