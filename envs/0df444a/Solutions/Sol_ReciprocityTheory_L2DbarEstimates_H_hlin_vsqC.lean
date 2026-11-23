-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.hlin_vsqC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:20.919099+00:00
-- url     : https://prove2.me/submissions/e0fd7db2-28d9-4d1b-aed6-1e7f432a64fb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_sqC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {p : ℕ} (w : Fin p → ℂ) : ((vsq w : ℝ) : ℂ) = ∑ i, w i * conj (w i) := by
  rw [vsq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => hlin_sqC (w i)
end ReciprocityTheory.L2DbarEstimates.H
