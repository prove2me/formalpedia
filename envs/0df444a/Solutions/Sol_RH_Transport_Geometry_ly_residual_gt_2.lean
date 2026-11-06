-- Prove2me | solution 2 for RH.Transport.Geometry.ly_residual_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:11.091364+00:00
-- url     : https://prove2.me/submissions/aa9b1bfe-e77a-47ae-9566-e59a4c74c20a

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
    (21 / 80 : ℝ) < ly p - d := by
  dsimp [ly]
  dsimp [ell] at hd
  linarith
end RH.Transport.Geometry
