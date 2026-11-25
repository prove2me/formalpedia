-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.isHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:56.602041+00:00
-- url     : https://prove2.me/submissions/f52c2b2f-6225-4d9d-8e7c-a74efe5066c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_continuous_Gm
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_me_Gm
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Gm_mem
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_map_lmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution : IsHaarOn (UWb 0 r) (μG r) := by
  refine ⟨?_, ?_, ?_, fun s hs => map_lmul s hs⟩
  · unfold μG; infer_instance
  · unfold μG
    rw [Ne, Measure.map_eq_zero_iff continuous_Gm.measurable.aemeasurable]
    intro h
    have h1 := AddCircle.measure_univ (2 * π)
    rw [h, Measure.coe_zero, Pi.zero_apply, eq_comm, ENNReal.ofReal_eq_zero] at h1
    linarith [Real.pi_pos]
  · unfold μG
    rw [me_Gm.map_apply]
    have : Gm r ⁻¹' {x | Matrix.of x ∉ UWb 0 r} = ∅ := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Gm_mem θ
    rw [this, measure_empty]
end PI.ExistsGaugeMeasureForEachRank.W
