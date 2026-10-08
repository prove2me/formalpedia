-- Prove2me | solution 1 for RetailVariety.Statics.lhs13_increasing_in_lam
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:23:36.584131+00:00
-- url     : https://prove2.me/submissions/e6e74bb0-dc1f-42f8-b1cd-0d80b14619de

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology
open RetailVariety.Statics


theorem solution (p c σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun lam : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
        * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi 0) ∧
      Tendsto (fun lam : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
        * Real.exp (criticalFractile p c ^ 2 / 2)) atTop atTop := by
  have hp : 0 < p := lt_trans hc hcp
  have ha : 0 < (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) := by
    apply mul_pos
    · have : c / p < 1 := (div_lt_one hp).mpr hcp
      linarith
    · exact div_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)) hσ
  have hb : 0 < 1 - β := by linarith
  have he : 0 < Real.exp (criticalFractile p c ^ 2 / 2) := Real.exp_pos _
  constructor
  · intro a ha' b hb' hab
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt ha') hab hb) ha) he
  · exact ((tendsto_rpow_atTop hb).const_mul_atTop ha).atTop_mul_const he

#print axioms solution
