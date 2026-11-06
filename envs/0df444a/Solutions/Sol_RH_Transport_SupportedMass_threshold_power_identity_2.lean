-- Prove2me | solution 2 for RH.Transport.SupportedMass.threshold_power_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:23:32.413913+00:00
-- url     : https://prove2.me/submissions/d2b47478-0cd8-430a-b80d-547938be8f6a

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z)
    (ell : ℝ) :
    (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _),
    ← Real.rpow_mul hZ.le]
  congr 2
  ring
end RH.Transport.SupportedMass
