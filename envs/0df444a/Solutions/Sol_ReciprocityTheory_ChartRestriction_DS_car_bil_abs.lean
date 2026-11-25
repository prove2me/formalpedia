-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_bil_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:50.715988+00:00
-- url     : https://prove2.me/submissions/33d29ac4-a2be-49d7-bc8b-6dc82b97681e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {R : Type*} [Ring R] (p1 m1 p2 m2 δ δ' : R) (h1 : m1 * p2 + p2 * m1 = δ)
    (h2 : m2 * p1 + p1 * m2 = δ') (hp : p1 * p2 + p2 * p1 = 0) (hm : m1 * m2 + m2 * m1 = 0) :
    p1 * m1 * (p2 * m2) - p2 * m2 * (p1 * m1) = p1 * δ * m2 - p2 * δ' * m1 := by
  have e1 : m1 * p2 = δ - p2 * m1 := eq_sub_of_add_eq h1
  have e2 : m2 * p1 = δ' - p1 * m2 := eq_sub_of_add_eq h2
  have e3 : p2 * p1 = -(p1 * p2) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hp)
  have e4 : m2 * m1 = -(m1 * m2) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hm)
  have e5 : p2 * (p1 * m2) * m1 = p1 * (p2 * m1) * m2 := by
    calc p2 * (p1 * m2) * m1 = p2 * p1 * (m2 * m1) := by simp only [mul_assoc]
      _ = p1 * p2 * (m1 * m2) := by rw [e3, e4, neg_mul_neg]
      _ = p1 * (p2 * m1) * m2 := by simp only [mul_assoc]
  calc p1 * m1 * (p2 * m2) - p2 * m2 * (p1 * m1)
        = p1 * (m1 * p2) * m2 - p2 * (m2 * p1) * m1 := by simp only [mul_assoc]
    _ = p1 * (δ - p2 * m1) * m2 - p2 * (δ' - p1 * m2) * m1 := by rw [e1, e2]
    _ = p1 * δ * m2 - p2 * δ' * m1 - (p1 * (p2 * m1) * m2 - p2 * (p1 * m2) * m1) := by
      simp only [mul_sub, sub_mul]; abel
    _ = p1 * δ * m2 - p2 * δ' * m1 := by rw [e5, sub_self, sub_zero]
end ReciprocityTheory.ChartRestriction.DS
