-- Prove2me | solution 2 for RH.Transport.Geometry.lx_residual_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:15:10.547977+00:00
-- url     : https://prove2.me/submissions/5fcc0d7d-ade2-4255-a344-223f3aa6225c

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
    (11 / 80 : ℝ) < lx p - d := by
  dsimp [lx]
  dsimp [ell] at hd
  linarith
end RH.Transport.Geometry
