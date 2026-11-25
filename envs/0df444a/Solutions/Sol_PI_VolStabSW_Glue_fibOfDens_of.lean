-- Prove2me | solution 1 for PI.VolStabSW.Glue.fibOfDens_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:40.271736+00:00
-- url     : https://prove2.me/submissions/192db192-665e-43b9-a390-0f4c184efe0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Theorems.Thm_PI_VolStabSW_Glue_fibG_integral
import Theorems.Thm_PI_VolStabSW_Glue_fibG_supp

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
namespace PI.VolStabSW.Glue
theorem _root_.solution (hDis : DisintStep) : FibOfDens := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hνp f ι U hf hι hr hU hD
  haveI := hμ
  haveI := hν
  haveI := hνp
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hfin : ∀ b K, IsCompact K → K ⊆ U → fibG hD hU b K < ⊤ := by
    intro b K hK hKU
    unfold fibG
    rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet]
    have hsub : K ⊆ Set.range (Subtype.val : U → V) := by
      rw [Subtype.range_coe]
      exact hKU
    exact ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff hsub).2 hK).measure_lt_top
  have hint : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fibG hD hU b)) ∧
      Continuous (fun b => ∫ v, φ v ∂(fibG hD hU b)) ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fibG hD hU b) ∂ν := by
    intro φ hφ
    have hG := G_spec hD hφ
    have heq : (fun b => ∫ v, φ v ∂(fibG hD hU b)) = G hD φ :=
      funext fun b => (fibG_integral hD hU b φ hφ).2
    refine ⟨fun b => (fibG_integral hD hU b φ hφ).1, ?_, ?_⟩
    · rw [heq]
      exact hG.1
    · intro S hS
      rw [heq]
      exact hG.2 S hS
  have hsupp := fibG_supp hD hU hf hι.continuous
  have hstep := hDis V X Y μ ν hμ hν hνp f ι U hf hι hr hU (fibG hD hU) hsupp hfin hint
  refine ⟨fibG hD hU, hsupp, hstep, fun φ hc hs hsub => ?_⟩
  have h3 := hint φ ⟨hc, hs, hsub⟩
  exact ⟨fun b _ => h3.1 b, h3.2.1.continuousOn⟩
end PI.VolStabSW.Glue
