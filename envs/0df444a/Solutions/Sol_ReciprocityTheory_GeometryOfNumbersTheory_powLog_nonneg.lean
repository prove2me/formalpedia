-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.powLog_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:58.213351+00:00
-- url     : https://prove2.me/submissions/13880d89-66b2-4d39-98c6-f34004b5470f

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt

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
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have : (0 : ℝ) ≤ n := by positivity
  exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
end ReciprocityTheory.GeometryOfNumbersTheory
