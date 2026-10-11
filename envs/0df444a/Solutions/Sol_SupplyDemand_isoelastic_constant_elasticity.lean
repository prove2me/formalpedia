-- Prove2me | solution 1 for SupplyDemand.isoelastic_constant_elasticity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:30:54.251982+00:00
-- url     : https://prove2.me/submissions/5fdd3fb0-7bf1-477b-be1a-8871e19a40eb

import Mathlib
import Definitions.Def_SupplyDemand_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SupplyDemand

theorem solution (P : ℝ) (hP : 0 < P) :
    pointElasticity isoelasticSupply P = 0.5 ∧
    pointElasticity isoelasticDemand P = -2 := by
  have hIdentity (a c : ℝ) (hc : c ≠ 0) :
      (c * (a * P ^ (a - 1))) * P / (c * P ^ a) = a := by
    have hpow : P ^ (a - 1) * P = P ^ a := by
      simpa only [Real.rpow_one, sub_add_cancel] using
        (Real.rpow_add hP (a - 1) 1).symm
    have hden : c * P ^ a ≠ 0 :=
      mul_ne_zero hc (ne_of_gt (Real.rpow_pos_of_pos hP a))
    calc
      (c * (a * P ^ (a - 1))) * P / (c * P ^ a)
          = a * (c * P ^ a) / (c * P ^ a) := by
              rw [← hpow]
              ring
      _ = a := by field_simp [hden]
  change
    deriv (fun x : ℝ => 5 * x ^ (0.5 : ℝ)) P * P /
      (5 * P ^ (0.5 : ℝ)) = (0.5 : ℝ) ∧
    deriv (fun x : ℝ => 3 * x ^ (-2 : ℝ)) P * P /
      (3 * P ^ (-2 : ℝ)) = (-2 : ℝ)
  constructor
  · rw [deriv_const_mul_field, Real.deriv_rpow_const]
    exact hIdentity (0.5 : ℝ) 5 (by norm_num)
  · rw [deriv_const_mul_field, Real.deriv_rpow_const]
    exact hIdentity (-2 : ℝ) 3 (by norm_num)
