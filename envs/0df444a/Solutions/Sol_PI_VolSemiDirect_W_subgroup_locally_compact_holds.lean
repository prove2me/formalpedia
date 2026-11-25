-- Prove2me | solution 1 for PI.VolSemiDirect.W.subgroup_locally_compact_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:10.112075+00:00
-- url     : https://prove2.me/submissions/f5827f36-c9e0-490a-bb45-241eace29f93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
namespace PI.VolSemiDirect.W
theorem _root_.solution : SubLCSC := by
  intro X _ _ Γ K hX hK hΓc hΓd
  obtain ⟨hlc, hsc, ht2, htg⟩ := hX
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := htg
  haveI := hΓc
  haveI := hΓd
  let f : ratG Γ K → Γ := fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩
  refine ⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology,
    inferInstance, inferInstance⟩, ?_, ?_⟩
  · have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg (fun y : Γ => (y : X)) h
      exact h'
    exact hf.countable
  · have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hemb : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hcont continuous_subtype_val
      show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology
end PI.VolSemiDirect.W
