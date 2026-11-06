-- Prove2me | solution 2 for RH.Transport.Geometry.h_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:54.570786+00:00
-- url     : https://prove2.me/submissions/a62d50a1-398e-495c-96cb-6129b99f23cb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : p < 1 / 30) : h p < 1 := by
  dsimp [h]
  linarith
end RH.Transport.Geometry
