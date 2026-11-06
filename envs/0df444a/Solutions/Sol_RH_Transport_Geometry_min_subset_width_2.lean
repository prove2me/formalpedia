-- Prove2me | solution 2 for RH.Transport.Geometry.min_subset_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:05.820438+00:00
-- url     : https://prove2.me/submissions/5c89bbb7-8c7b-44c1-892b-3d27e8fe75e1

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
    subsetWidth p (ell p) = 1 / 2 - 3 * p := by
  dsimp [subsetWidth, width, ell]
  ring
end RH.Transport.Geometry
