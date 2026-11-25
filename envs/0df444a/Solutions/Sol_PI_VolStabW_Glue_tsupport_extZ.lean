-- Prove2me | solution 1 for PI.VolStabW.Glue.tsupport_extZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:49.626358+00:00
-- url     : https://prove2.me/submissions/276de78a-139e-4996-b934-590e64262d2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue

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
namespace PI.VolStabW.Glue
theorem _root_.solution (U : Set V) (φ : U → ℝ) (hs : HasCompactSupport φ) :
    tsupport (extZ U φ) ⊆ Subtype.val '' tsupport φ := by
  have hK : IsCompact (Subtype.val '' tsupport φ) := hs.image continuous_subtype_val
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra h
  apply hv
  by_cases hU : v ∈ U
  · simp only [extZ, hU, dite_true]
    exact image_eq_zero_of_notMem_tsupport (fun hm => h ⟨⟨v, hU⟩, hm, rfl⟩)
  · simp [extZ, hU]
end PI.VolStabW.Glue
