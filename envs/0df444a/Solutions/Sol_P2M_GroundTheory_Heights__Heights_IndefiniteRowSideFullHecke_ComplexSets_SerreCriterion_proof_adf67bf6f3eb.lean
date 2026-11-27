-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreCriterion_proof_adf67bf6f3eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:55.529799+00:00
-- url     : https://prove2.me/submissions/c8d16a9a-3a1d-412c-9d1e-6c12f83290a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one_9a5aa6b317f3

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
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SerreCriterion
theorem _root_.solution (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _
end SerreCriterion
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
