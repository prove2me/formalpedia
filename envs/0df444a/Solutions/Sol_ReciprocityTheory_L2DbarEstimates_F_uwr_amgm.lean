-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.uwr_amgm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:33.495888+00:00
-- url     : https://prove2.me/submissions/30dae4fb-3eb2-4716-b41f-5a86719c228d

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
theorem _root_.solution (A B p : ℝ) : A * B ≤ A ^ 2 * Real.exp (-p) + B ^ 2 * Real.exp p := by
  rw [Real.exp_neg]
  have he := Real.exp_pos p
  have key : 0 ≤ A ^ 2 + B ^ 2 * Real.exp p ^ 2 - A * B * Real.exp p := by
    nlinarith [sq_nonneg (A - B * Real.exp p / 2), sq_nonneg (B * Real.exp p)]
  have h2 : A ^ 2 * (Real.exp p)⁻¹ + B ^ 2 * Real.exp p - A * B
      = (A ^ 2 + B ^ 2 * Real.exp p ^ 2 - A * B * Real.exp p) / Real.exp p := by
    field_simp
  have h3 := div_nonneg key he.le
  linarith
end ReciprocityTheory.L2DbarEstimates.F
