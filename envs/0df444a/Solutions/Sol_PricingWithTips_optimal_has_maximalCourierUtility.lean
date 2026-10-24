-- Prove2me | solution 1 for PricingWithTips.optimal_has_maximalCourierUtility
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:12:21.429123+00:00
-- url     : https://prove2.me/submissions/cc73bd4c-87a4-4cf8-b175-8237bf2e1709

import Theorems.Thm_PricingWithTips_optimal_has_courier_plan
import Theorems.Thm_PricingWithTips_maximalCourierUtility_exists_of_plan

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    ∃ uBar : D → ℝ, IsMaximalCourierUtility M A uBar := by
  exact maximalCourierUtility_exists_of_plan M A
    (optimal_has_courier_plan M A hoptimal) hnotfull
