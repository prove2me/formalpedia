-- Prove2me | solution 2 for RH.Transport.Geometry.boundary_decrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:50.291423+00:00
-- url     : https://prove2.me/submissions/2088e2ff-0266-42a2-957b-56abf2a4c59d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution (p : ℝ) :
    (7 / 8 : ℝ) - boundary p = p / 4 := by
  dsimp [boundary]
  ring
end RH.Transport.Geometry
