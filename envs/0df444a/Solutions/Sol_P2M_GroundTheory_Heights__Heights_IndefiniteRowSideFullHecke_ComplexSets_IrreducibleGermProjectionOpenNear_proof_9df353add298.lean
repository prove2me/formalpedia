-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleGermProjectionOpenNear_proof_9df353add298
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:31.249431+00:00
-- url     : https://prove2.me/submissions/f99cb3ca-2bae-4df4-a9dc-131464d5e133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermProjectionOpenNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermProjectionImageNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermProjectionOpenNear

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
namespace IrreducibleGermProjectionOpenNear
theorem _root_.solution (hiso : IsolatedFibreNear.Statement)
    (himg : IrreducibleGermProjectionImageNear.Statement) (hopen : FiniteGermProjectionOpenAt.Statement) :
    IrreducibleGermProjectionOpenNear.Statement := by
  intro σ _ X w d A hX hirr hisow hinj
  obtain ⟨N₁, hN₁, h₁⟩ := hiso σ X w d A hX hisow
  obtain ⟨N₂, hN₂, h₂⟩ := himg σ X w d A hX hirr hisow hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩
  rintro x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV

  have hXx : IsAnalyticNear X x := ⟨N, k, f, hNo, hxN, hf, hXN⟩
  exact hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV
end IrreducibleGermProjectionOpenNear
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
