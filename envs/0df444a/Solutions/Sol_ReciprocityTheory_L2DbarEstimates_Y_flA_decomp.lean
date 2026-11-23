-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:38.095368+00:00
-- url     : https://prove2.me/submissions/80c33f07-251e-4711-b6f2-e7caea045106

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [flA_expand w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcb : w b • bas n b = (w b).re • bas n b + (w b).im • (I • bas n b) := by
    conv_lhs => rw [← Complex.re_add_im (w b)]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hcb, map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf; simp only [I_sq]; ring_nf
end ReciprocityTheory.L2DbarEstimates.Y
