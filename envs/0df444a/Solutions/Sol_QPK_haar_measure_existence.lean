-- Prove2me | solution 1 for QPK.haar_measure_existence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:31.861838+00:00
-- url     : https://prove2.me/submissions/364200d9-ce7d-4532-ae34-2ba6be6a5fe8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Theorems.Thm_QPK_map_val_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution : HaarExist := by
  intro G _ _ _ _ _ _ _ _ K hKc hK
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H → G) := hHc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  have hv : Measurable (Subtype.val : H → G) := measurable_subtype_coe
  let α : Measure H := Measure.haar
  have hfin : IsFiniteMeasureOnCompacts (α.map Subtype.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hv hC.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hC).measure_lt_top
  refine ⟨α.map Subtype.val, ⟨?_, ?_, ?_, ?_⟩, hfin, ?_⟩
  · infer_instance
  · intro h
    rw [Measure.map_eq_zero_iff hv.aemeasurable] at h
    exact (Measure.measure_univ_pos.mp (isOpen_univ.measure_pos α Set.univ_nonempty)) h
  · rw [Measure.map_apply hv hKc.measurableSet.compl]
    have h : (Subtype.val : H → G) ⁻¹' Kᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [h, measure_empty]
  · intro s hs
    have h := map_val_mul H ⟨s, hs⟩ α
    rw [map_mul_left_eq_self] at h
    exact h.symm
  · intro U hU ⟨x, hxU, hxK⟩
    rw [Measure.map_apply hv hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_ne_zero α ⟨⟨x, hxK⟩, hxU⟩
end QPK
