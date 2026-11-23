-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.vsq_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:18.878146+00:00
-- url     : https://prove2.me/submissions/ca860edc-c73e-4d63-af17-9fce4d31d05a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {p : ℕ} (w : Fin p → ℂ) (hw : w ≠ 0) : 0 < vsq w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := by simpa using hi
  have h1 : 0 < ‖w i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi') 2
  have h2 : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  exact lt_of_lt_of_le h1 h2
end ReciprocityTheory.L2DbarEstimates.H
