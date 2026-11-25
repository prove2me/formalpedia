-- Prove2me | solution 1 for PI.VolStabSW.Glue.fibG_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:14.09781+00:00
-- url     : https://prove2.me/submissions/d5d48c11-0bd1-4260-93fd-c0444633fe62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Theorems.Thm_PI_VolStabSW_Glue_lam_apply
import Theorems.Thm_PI_VolStabSW_Glue_extZ_restr

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
theorem _root_.solution (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) (φ : V → ℝ)
    (h : IsCcOn U φ) :
    Integrable φ (fibG hD hU b) ∧ ∫ v, φ v ∂(fibG hD hU b) = G hD φ b := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hme : MeasurableEmbedding (Subtype.val : U → V) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  unfold fibG
  refine ⟨?_, ?_⟩
  · rw [hme.integrable_map_iff]
    exact (restr hU φ h).continuous.integrable_of_hasCompactSupport
      (restr hU φ h).hasCompactSupport
  · rw [hme.integral_map]
    have hR := RealRMK.integral_rieszMeasure (lam hD hU b) (restr hU φ h)
    rw [lam_apply, extZ_restr] at hR
    exact hR
end PI.VolStabSW.Glue
