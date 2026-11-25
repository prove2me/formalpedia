-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.uwr_boundS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:38.746674+00:00
-- url     : https://prove2.me/submissions/efd372ef-725b-4cc0-b80a-921318eac39d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (E s t α q P N : ℝ) (hE : 0 < E) (hq : 0 ≤ q)
    (hsq : s ^ 2 ≤ 2 * q) (hN0 : 0 ≤ N) (hN : N ≤ E * (s + 2 * α * t)) :
    N ^ 2 ≤ (4 * E ^ 2 * Real.exp P + 8 * E * α ^ 2) * (q * Real.exp (-P) + t ^ 2 * E) := by
  have hP : Real.exp P * Real.exp (-P) = 1 := by
    rw [← Real.exp_add]
    simp
  have hEP := Real.exp_pos P
  have hEm := Real.exp_pos (-P)
  have h1 : N ^ 2 ≤ (E * (s + 2 * α * t)) ^ 2 := by nlinarith
  have h2 : (s + 2 * α * t) ^ 2 ≤ 4 * q + 8 * α ^ 2 * t ^ 2 := by
    nlinarith [sq_nonneg (s - 2 * α * t)]
  have h3 : N ^ 2 ≤ E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) := by
    calc N ^ 2 ≤ (E * (s + 2 * α * t)) ^ 2 := h1
      _ = E ^ 2 * (s + 2 * α * t) ^ 2 := by ring
      _ ≤ E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) := by gcongr
  have e1 : 0 ≤ 4 * E ^ 3 * t ^ 2 * Real.exp P := by positivity
  have e2 : 0 ≤ 8 * E * α ^ 2 * q * Real.exp (-P) := by positivity
  have key : (4 * E ^ 2 * Real.exp P + 8 * E * α ^ 2) * (q * Real.exp (-P) + t ^ 2 * E)
      = E ^ 2 * (4 * q + 8 * α ^ 2 * t ^ 2) + 4 * E ^ 3 * t ^ 2 * Real.exp P +
        8 * E * α ^ 2 * q * Real.exp (-P) := by
    linear_combination (4 * E ^ 2 * q) * hP
  rw [key]
  linarith
end ReciprocityTheory.L2DbarEstimates.F
