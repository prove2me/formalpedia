-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrable_volumeIoiPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:49.881289+00:00
-- url     : https://prove2.me/submissions/9023381d-23ae-4af5-830b-d9630fbf6676

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]
end ReciprocityTheory.MultiplicativeHeights
