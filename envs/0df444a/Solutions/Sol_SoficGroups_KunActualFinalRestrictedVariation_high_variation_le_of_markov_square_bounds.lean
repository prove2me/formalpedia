-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.high_variation_le_of_markov_square_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/450d5ba3-e3bd-4372-af3e-994b86d0a309

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {d t α η b r E H : ℝ}
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hbase : b ^ 2 ≤ t)
    (hresidual : r ≤ η * b)
    (henergy : E ≤ 2 * d * Real.sqrt t * r)
    (hcauchy : H ^ 2 ≤ 3 * d * t * E)
    (hsmall : 486 * d ^ 2 * η ≤ 4 * α ^ 2) :
    9 * H ≤ 2 * α * t := by
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hb_sqrt : b ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hbase
  have hr_sqrt : r ≤ η * Real.sqrt t :=
    hresidual.trans (mul_le_mul_of_nonneg_left hb_sqrt hη)
  have henergy' : E ≤ 2 * d * η * t := by
    calc
      E ≤ 2 * d * Real.sqrt t * r := henergy
      _ ≤ 2 * d * Real.sqrt t * (η * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hr_sqrt
          (mul_nonneg (mul_nonneg (by norm_num) hd) hsqrt)
      _ = 2 * d * η * (Real.sqrt t) ^ 2 := by ring
      _ = 2 * d * η * t := by rw [hsqrt_sq]
  have hcauchy' : H ^ 2 ≤ 6 * d ^ 2 * η * t ^ 2 := by
    calc
      H ^ 2 ≤ 3 * d * t * E := hcauchy
      _ ≤ 3 * d * t * (2 * d * η * t) :=
        mul_le_mul_of_nonneg_left henergy'
          (mul_nonneg (mul_nonneg (by norm_num) hd) ht)
      _ = 6 * d ^ 2 * η * t ^ 2 := by ring
  have hsquare : (9 * H) ^ 2 ≤ (2 * α * t) ^ 2 := by
    have hsmall' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
    nlinarith
  nlinarith [mul_nonneg hα ht]
end SoficGroups.KunActualFinalRestrictedVariation
