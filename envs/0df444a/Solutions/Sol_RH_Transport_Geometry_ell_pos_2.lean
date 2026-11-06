-- Prove2me | solution 2 for RH.Transport.Geometry.ell_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:54.052946+00:00
-- url     : https://prove2.me/submissions/b1f435b1-16a6-4236-8d82-a4a8ae8fdd2c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : 0 < p) : 0 < ell p := by
  dsimp [ell]
  linarith
end RH.Transport.Geometry
