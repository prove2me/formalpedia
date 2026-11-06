-- Prove2me | solution 2 for RH.Transport.Geometry.subset_width_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:00.077188+00:00
-- url     : https://prove2.me/submissions/a9b34d45-8dd7-462d-baaf-e73a2cc00e59

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution (p d : ℝ) :
    subsetWidth p d + subsetEll p d - 1 = -3 * d := by
  dsimp [subsetWidth, subsetEll, width, ell]
  ring
end RH.Transport.Geometry
