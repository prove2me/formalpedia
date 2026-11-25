-- Prove2me | solution 1 for PI.VolStabW.Glue.fibG_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:20.533094+00:00
-- url     : https://prove2.me/submissions/d2286c81-436b-4aaf-944d-a79cb13256be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Theorems.Thm_PI_VolStabW_Glue_lam_apply
import Theorems.Thm_PI_VolStabW_Glue_extZ_restr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.Glue
open MeasureTheory Topology Set Filter PI.VolStabW
open scoped CompactlySupported
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} {U : Set V}
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
variable [OpensMeasurableSpace V]
namespace PI.VolStabW.Glue
theorem _root_.solution (hD : DensAll μ f ι ν U) (hU : IsOpen U) (b : X) (φ : V → ℝ)
    (h : IsCcOn U φ) :
    Integrable φ (fibG hD hU b) ∧ ∫ v, φ v ∂(fibG hD hU b) = G hD φ b := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hme : MeasurableEmbedding (Subtype.val : U → V) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hint : Integrable (restr hU φ h) (RealRMK.rieszMeasure (lam hD hU b)) :=
    (restr hU φ h).continuous.integrable_of_hasCompactSupport (restr hU φ h).hasCompactSupport
  refine ⟨(hme.integrable_map_iff).2 hint, ?_⟩
  rw [fibG, hme.integral_map]
  have := RealRMK.integral_rieszMeasure (lam hD hU b) (restr hU φ h)
  rw [lam_apply, extZ_restr] at this
  exact this
end PI.VolStabW.Glue
