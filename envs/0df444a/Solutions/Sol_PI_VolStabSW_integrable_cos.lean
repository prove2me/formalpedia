-- Prove2me | solution 1 for PI.VolStabSW.integrable_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:32.415913+00:00
-- url     : https://prove2.me/submissions/bb1ce114-1845-4f3d-ab5b-e210c3688189

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Theorems.Thm_PI_VolStabSW_isCompact_cos

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
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabSW
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hK := isCompact_cos Λ hΛc y
  have hO : IsOpen {z : V | z - y ∈ Λ} := hΛo.preimage (continuous_sub_right y)
  have hI : IntegrableOn (fun _ : V => (1 : ℝ)) {z : V | z - y ∈ Λ} μ := by
    first
      | exact ContinuousOn.integrableOn_compact hK continuousOn_const
      | exact integrableOn_const hK.measure_lt_top.ne
      | exact integrableOn_const.2 (Or.inr hK.measure_lt_top)
  exact hI.integrable_indicator hO.measurableSet
end PI.VolStabSW
