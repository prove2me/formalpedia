-- Prove2me | solution 1 for PI.VolStabSW.Glue.extZ_restr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:38.875422+00:00
-- url     : https://prove2.me/submissions/9f5bbb46-1625-4a06-8efe-eabddf73518b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.Glue
open MeasureTheory Topology Set Filter PI.VolStabSW
open scoped CompactlySupported
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]
namespace PI.VolStabSW.Glue
theorem _root_.solution (hU : IsOpen U) (φ : V → ℝ) (h : IsCcOn U φ) :
    extZ U (restr hU φ h) = φ := by
  funext v
  by_cases hv : v ∈ U
  · simp only [extZ, dif_pos hv]
    rfl
  · simp only [extZ, dif_neg hv]
    exact (image_eq_zero_of_notMem_tsupport fun ht => hv (h.2.2 ht)).symm
end PI.VolStabSW.Glue
