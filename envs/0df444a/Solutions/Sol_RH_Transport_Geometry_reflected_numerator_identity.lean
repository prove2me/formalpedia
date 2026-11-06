-- Prove2me | solution 1 for RH.Transport.Geometry.reflected_numerator_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:00.840978+00:00
-- url     : https://prove2.me/submissions/11f4756e-19c9-4fdb-b55e-84870d0786d2

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
    1 + 3 * subsetEll p d - 2 * subsetWidth p d =
      5 * ell p - 1 + d := by
  dsimp [subsetEll, subsetWidth, ell, width]
  ring
end RH.Transport.Geometry
