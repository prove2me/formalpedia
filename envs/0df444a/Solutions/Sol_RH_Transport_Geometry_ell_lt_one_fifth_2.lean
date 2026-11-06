-- Prove2me | solution 2 for RH.Transport.Geometry.ell_lt_one_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:23:12.448218+00:00
-- url     : https://prove2.me/submissions/bfe8c5e5-338d-430e-a50e-4fd02109f18b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution {p : ℝ} (hp : p < 1 / 30) :
    ell p < 1 / 5 := by
  dsimp [ell]
  linarith
end RH.Transport.Geometry
