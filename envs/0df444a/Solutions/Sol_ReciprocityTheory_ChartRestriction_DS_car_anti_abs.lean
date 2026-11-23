-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_anti_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:36.193495+00:00
-- url     : https://prove2.me/submissions/ebaa9cb1-c3c2-4e92-ae6c-517a6b181d8a

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
theorem _root_.solution {R : Type*} [Ring R] (A B c e : R) (hcB : c * B = B * c) (heA : e * A = A * e)
    (hAB : A * B = B * A) (hce : c * e = -(e * c)) : A * c * (B * e) = -(B * e * (A * c)) := by
  calc A * c * (B * e) = A * (c * B) * e := by simp only [mul_assoc]
    _ = A * (B * c) * e := by rw [hcB]
    _ = A * B * (c * e) := by simp only [mul_assoc]
    _ = B * A * -(e * c) := by rw [hAB, hce]
    _ = -(B * (A * e) * c) := by simp only [mul_neg, mul_assoc]
    _ = -(B * (e * A) * c) := by rw [heA]
    _ = -(B * e * (A * c)) := by simp only [mul_assoc]
end ReciprocityTheory.ChartRestriction.DS
