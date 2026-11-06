-- Prove2me | solution 1 for RH.Transport.SupportedMass.support_decay_absorbs_row_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:41.152048+00:00
-- url     : https://prove2.me/submissions/40effd7d-c374-4e8a-bc8e-d6d3a3a273f3

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_half_decay_exponent_nonpos

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {p d Z mass C : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * Geometry.ell p - 1 + d) / 8) ≤ C := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := half_decay_exponent_nonpos hp hd
  have hr : Z ^ (-d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ he
  calc
    _ ≤ (C * Z ^ (-d / 2)) *
        Z ^ (max 0 (5 * Geometry.ell p - 1 + d) / 8) :=
      mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hZ0.le _)
    _ = C * Z ^ (-d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8) := by
      rw [Real.rpow_add hZ0]
      ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hr hC
    _ = C := mul_one C
end RH.Transport.SupportedMass
