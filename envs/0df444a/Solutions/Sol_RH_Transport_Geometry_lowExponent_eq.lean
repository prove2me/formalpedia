-- Prove2me | solution 1 for RH.Transport.Geometry.lowExponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:24.51876+00:00
-- url     : https://prove2.me/submissions/186934e3-e1ee-4c82-a484-f6d6ae1f8649

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
    lowExponent p = 3 / 16 - p / 4 := by
  dsimp [lowExponent, lx, b]
  ring
end RH.Transport.Geometry
