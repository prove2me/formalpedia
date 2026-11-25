-- Prove2me | solution 1 for PI.VolStabW.cosApx_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:57.24517+00:00
-- url     : https://prove2.me/submissions/779b0855-42c5-40f3-9ddb-85db8de2c166

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
import Theorems.Thm_PI_VolStabW_cosApx_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
omit [MeasurableSpace V] [OpensMeasurableSpace V]
namespace PI.VolStabW
theorem _root_.solution (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | -x + y ∈ Λ}, hΛ.preimage (continuous_const.add continuous_id), ?_,
    fun y hy => cosApx_eq Λ φ hy⟩
  show -x + x ∈ Λ
  rw [neg_add_cancel]
  exact Λ.zero_mem
end PI.VolStabW
