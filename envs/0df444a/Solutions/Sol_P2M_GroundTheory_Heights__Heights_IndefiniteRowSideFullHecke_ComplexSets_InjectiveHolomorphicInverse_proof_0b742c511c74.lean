-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_proof_0b742c511c74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:06.907722+00:00
-- url     : https://prove2.me/submissions/b225bb0c-bffa-47f3-8b45-9b20e58a698e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicInverse
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_exists_equiv_ff0699fdad70

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
open Filter Topology
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
theorem _root_.solution (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse
