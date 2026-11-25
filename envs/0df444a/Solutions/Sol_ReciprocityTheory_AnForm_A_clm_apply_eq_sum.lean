-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.clm_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:11.618279+00:00
-- url     : https://prove2.me/submissions/2148b1fd-99bf-40e0-a1f8-a21d53b2b518

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (c : ι → ℝ) :
    L c = ∑ j, c j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (c j) : ι → ℝ) = c j • (Pi.single j 1 : ι → ℝ) := by
    funext k; by_cases h : k = j <;> simp [h]
  rw [this, map_smul, smul_eq_mul]
end ReciprocityTheory.AnForm.A
