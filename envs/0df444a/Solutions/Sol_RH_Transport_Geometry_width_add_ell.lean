-- Prove2me | solution 1 for RH.Transport.Geometry.width_add_ell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:18.856989+00:00
-- url     : https://prove2.me/submissions/15fb039f-5be5-471e-b963-7914fa1a1648

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution (p : ℝ) : width p + ell p = 1 := by
  dsimp [width, ell]
  ring
end RH.Transport.Geometry
