-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.perpTrace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:42.918223+00:00
-- url     : https://prove2.me/submissions/9baeb297-c1ad-408b-a76e-9779d93aeca2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsq_pos

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
theorem _root_.solution : PerpTraceStatement := by
  intro p g hg
  have hs := hlin_vsq_pos hg
  refine ⟨fun i => sub_nonneg.mpr ((div_le_one hs).mpr
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))), ?_⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  change _ - vsq g / vsq g = _
  rw [div_self hs.ne']
  simp
end ReciprocityTheory.L2DbarEstimates.H
