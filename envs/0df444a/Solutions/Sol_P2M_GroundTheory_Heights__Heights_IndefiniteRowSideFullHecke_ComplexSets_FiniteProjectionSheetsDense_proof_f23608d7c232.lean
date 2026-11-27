-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionSheetsDense_proof_f23608d7c232
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:26.580475+00:00
-- url     : https://prove2.me/submissions/8b347015-5c29-4f91-abf1-c7e7a2891989

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetsDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionOffZerosDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionSheetsDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteProjectionSheetsDense
theorem _root_.solution (hP : IrreducibleGermPrimitiveForm.Statement)
    (hG : PrimitiveFormSheetedOffDiscriminant.Statement) (hD : FiniteProjectionOffZerosDense.Statement) :
    FiniteProjectionSheetsDense.Statement := by
  intro σ _ X w d A hX hI hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hP σ X w d A hX hI hiso hinj
  obtain ⟨M, hM, hsh⟩ := hG σ X w d A hX hI hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  obtain ⟨N', hN', hcl⟩ := hD σ X w d A hX hI hiso hinj δ hδ hδ0
  refine ⟨interior M ∩ N', Filter.inter_mem (interior_mem_nhds.2 hM) hN', ?_⟩
  rintro z ⟨hzX, hzM, hzN⟩
  have hzc := hcl ⟨hzX, hzN⟩
  rw [mem_closure_iff_nhds] at hzc ⊢
  intro U hU
  obtain ⟨y, ⟨hyU, hyM⟩, hyX, hyδ⟩ :=
    hzc (U ∩ interior M) (Filter.inter_mem hU (isOpen_interior.mem_nhds hzM))
  exact ⟨y, hyU, hyX, hsh y ⟨hyX, interior_subset hyM⟩ hyδ⟩
end FiniteProjectionSheetsDense
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
