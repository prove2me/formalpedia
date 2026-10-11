-- Prove2me | solution 1 for SupplyDemand.isoelastic_loglinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:26:26.318981+00:00
-- url     : https://prove2.me/submissions/9460f6e9-5c4b-48e5-9445-39782fc33f2f

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (P : ℝ) (hP : 0 < P) :
    Real.log (isoelasticSupply P) = Real.log 5 + 0.5 * Real.log P ∧
    Real.log (isoelasticDemand P) = Real.log 3 - 2 * Real.log P := by
  change Real.log (5 * P ^ (0.5 : ℝ)) = Real.log 5 + 0.5 * Real.log P ∧
    Real.log (3 * P ^ (-2 : ℝ)) = Real.log 3 - 2 * Real.log P
  constructor
  · rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_rpow hP]
  · rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_rpow hP]
    ring
