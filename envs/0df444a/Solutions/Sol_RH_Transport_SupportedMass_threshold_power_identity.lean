-- Prove2me | solution 1 for RH.Transport.SupportedMass.threshold_power_identity
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:01:06.82431+00:00
-- url     : https://prove2.me/submissions/549a7ee8-7148-4611-8953-dbb01823e7f3

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem solution {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z)
    (ell : ℝ) :
    (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le ell)]
  congr 1
  rw [← Real.rpow_mul hZ.le]
  congr 1
  ring
