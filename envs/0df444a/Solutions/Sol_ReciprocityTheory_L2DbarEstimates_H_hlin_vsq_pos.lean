-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.hlin_vsq_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:46.915785+00:00
-- url     : https://prove2.me/submissions/7cb264bb-3cb4-43a7-bcf4-ac81efe7c1e3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos

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
theorem _root_.solution {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖g j‖) (Finset.mem_univ i))
end ReciprocityTheory.L2DbarEstimates.H
