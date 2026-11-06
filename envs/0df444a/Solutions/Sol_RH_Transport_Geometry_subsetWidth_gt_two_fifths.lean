-- Prove2me | solution 1 for RH.Transport.Geometry.subsetWidth_gt_two_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:06.590316+00:00
-- url     : https://prove2.me/submissions/e7b9d671-aff7-4fb1-b409-23b7025fe5c9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : d ≤ ell p) :
    (2 / 5 : ℝ) < subsetWidth p d := by
  dsimp [subsetWidth, width]
  dsimp [ell] at hd
  linarith
end RH.Transport.Geometry
