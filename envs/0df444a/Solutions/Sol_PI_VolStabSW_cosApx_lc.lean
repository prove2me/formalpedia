-- Prove2me | solution 1 for PI.VolStabSW.cosApx_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:01.410966+00:00
-- url     : https://prove2.me/submissions/698b17da-616a-4bba-9c83-8c1a64c05ba3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Theorems.Thm_PI_VolStabSW_cosApx_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
omit [MeasurableSpace V] [OpensMeasurableSpace V]
namespace PI.VolStabSW
theorem _root_.solution (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : V => -x + y := continuous_const.add continuous_id
  have hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x :=
    (hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)
  filter_upwards [hm] with y hy
  exact cosApx_eq Λ φ hy
end PI.VolStabSW
