-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.powLog_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:48.92116+00:00
-- url     : https://prove2.me/submissions/eeb5e795-e231-43bb-882d-6155dc8092d6

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
theorem _root_.solution (D : ℕ) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) ^ D * Real.log ((m : ℝ) + 1) ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hl0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul (pow_le_pow_left₀ hm0 hmn D) hl hl0 (by positivity)
end ReciprocityTheory.GeometryOfNumbersTheory
