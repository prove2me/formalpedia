-- Prove2me | solution 2 for RH.Transport.Geometry.gram_margin_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:12.086756+00:00
-- url     : https://prove2.me/submissions/9ac0ac4b-eb4f-4c0e-81ea-70193141380a

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
    (1 / 30 : ℝ) < ly p - d - 11 * b / 6 := by
  dsimp [ly, b]
  dsimp [ell] at hd
  linarith
end RH.Transport.Geometry
