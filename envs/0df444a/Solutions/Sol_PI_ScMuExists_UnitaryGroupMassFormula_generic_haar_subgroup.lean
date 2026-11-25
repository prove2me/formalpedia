-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.generic_haar_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:09.190954+00:00
-- url     : https://prove2.me/submissions/282f63c2-da98-49e4-9883-c9282c6051a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HaarSub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : GenHaarSub := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val := rfl
  have hmeas : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤ := by
    intro C hC
    rw [hm, Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩
  refine ⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩
  · intro h0
    rw [hm, Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])
  · rw [hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]
    have hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact x.2
    rw [hpre, measure_empty]
  · intro s hs
    rw [hm, Measure.map_map (measurable_const_mul s) hmeas]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) =
        Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]
    congr 1
    first
      | exact map_mul_left_eq_self (Measure.haar : Measure K) _
      | exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _
  · intro U hU h1
    rw [hm, Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩
end PI.ScMuExists.UnitaryGroupMassFormula
