-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.growth_on_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:26:09.927101+00:00
-- url     : https://prove2.me/submissions/f8850d4a-b70a-4309-98c3-66220aa76360

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_NormVanishOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution (n m : ℕ) (C : ℝ) (t : ℂ) (w : V n) :
    max (C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)) 0 ≤
      max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
  have hr : 0 ≤ ‖t • w‖ := norm_nonneg _
  have hP : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) = (Real.sqrt (1 + ‖t • w‖ ^ 2)) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  have hs : Real.sqrt (1 + ‖t • w‖ ^ 2) ≤ (1 + ‖w‖) * (1 + ‖t‖) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [norm_smul]
    have ht := norm_nonneg t
    have hw := norm_nonneg w
    nlinarith [mul_nonneg ht hw, mul_nonneg (mul_nonneg ht hw) ht, mul_nonneg (mul_nonneg ht hw) hw]
  have hQ : (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) ≤ ((1 + ‖w‖) * (1 + ‖t‖)) ^ m := by
    rw [hP]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs m
  have hQ0 : 0 ≤ (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) := by positivity
  refine max_le ?_ (by positivity)
  calc C * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2)
      ≤ max C 0 * (1 + ‖t • w‖ ^ 2) ^ ((m : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
    _ ≤ max C 0 * ((1 + ‖w‖) * (1 + ‖t‖)) ^ m :=
        mul_le_mul_of_nonneg_left hQ (le_max_right _ _)
end ReciprocityTheory.L2DbarEstimates.Norm
