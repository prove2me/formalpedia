-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.smoothR_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:52.438048+00:00
-- url     : https://prove2.me/submissions/04c4adf1-4038-49a7-82ef-08f0138c3b4f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothR_const n z 1
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 := SmoothR.mul n z _ _ h1 h2
    simpa [Finset.prod_insert ha] using h3
end ReciprocityTheory.L2DbarEstimates
