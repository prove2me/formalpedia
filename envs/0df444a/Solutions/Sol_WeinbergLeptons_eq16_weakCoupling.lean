-- Prove2me | solution 1 for WeinbergLeptons.eq16_weakCoupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T00:30:10.882497+00:00
-- url     : https://prove2.me/submissions/5d1b178b-eede-45ea-a6ba-6a7ec5c1f957

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g lam : ℝ) (hg : g ≠ 0) (hlam : lam ≠ 0) :
    weakCoupling g lam / Real.sqrt 2 = 1 / (2 * lam ^ 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold weakCoupling wMass
  field_simp
  ring
