-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.discI_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:00.036884+00:00
-- url     : https://prove2.me/submissions/18a92ebb-973a-40d6-a097-246c6957d737

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_discI_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {R : ℝ} (hR : 0 ≤ R) : discI 0 R = Real.pi * R ^ 2 := by
  rw [pgds_discI_eq 0 hR]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
