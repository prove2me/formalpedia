-- Prove2me | solution 1 for RH.Transport.Geometry.width_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:16.955461+00:00
-- url     : https://prove2.me/submissions/44c08647-74ea-4907-be2e-c632399030fa

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry

set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section
namespace RH.Transport.Geometry
theorem _root_.solution (p : ℝ) : width p = lx p + ly p := by
  dsimp [width, lx, ly]
  ring
end RH.Transport.Geometry
