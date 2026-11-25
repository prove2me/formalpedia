-- Prove2me | solution 1 for PI.VolStabW.Glue.fibOfDens_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:08.88986+00:00
-- url     : https://prove2.me/submissions/28163c6d-296c-4d86-8733-173acef98565

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Theorems.Thm_PI_VolStabW_Glue_fibG_integral
import Theorems.Thm_PI_VolStabW_Glue_fibG_supp

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
namespace PI.VolStabW.Glue
theorem _root_.solution (hDis : DisintStep) : FibOfDens := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hpos f ι U hf hι hr hU hD
  refine ⟨fibG hD hU, fibG_supp hD hU hf hι.continuous, ?_, fun φ hc hs hsu => ?_⟩
  · have hint : ∀ φ : V → ℝ, IsCcOn U φ → (fun b => ∫ v, φ v ∂(fibG hD hU b)) = G hD φ :=
      fun φ h => funext fun b => (fibG_integral hD hU b φ h).2
    refine hDis V X Y μ ν hμ hν hpos f ι U hf hι hr hU (fibG hD hU)
      (fibG_supp hD hU hf hι.continuous) (fun b K hK hKU => ?_) (fun φ h => ?_)
    · haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
      have hme : MeasurableEmbedding (Subtype.val : U → V) :=
        MeasurableEmbedding.subtype_coe hU.measurableSet
      rw [fibG, hme.map_apply]
      have hsub : K ⊆ Set.range (Subtype.val : U → V) := by rw [Subtype.range_coe]; exact hKU
      exact ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).2 hK).measure_lt_top
    · refine ⟨fun b => (fibG_integral hD hU b φ h).1, ?_, fun S hS => ?_⟩
      · rw [hint φ h]; exact (G_spec hD h).1
      · rw [hint φ h]; exact (G_spec hD h).2 S hS
  · have h : IsCcOn U φ := ⟨hc, hs, hsu⟩
    refine ⟨fun b _ => (fibG_integral hD hU b φ h).1, ?_⟩
    have : (fun b => ∫ v, φ v ∂(fibG hD hU b)) = G hD φ :=
      funext fun b => (fibG_integral hD hU b φ h).2
    rw [this]; exact (G_spec hD h).1.continuousOn
end PI.VolStabW.Glue
