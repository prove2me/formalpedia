-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolGermsIntegrallyClosed_proof_f14d51847cc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:44.805802+00:00
-- url     : https://prove2.me/submissions/304685e1-a94c-4b03-940d-b3c2bf60f148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsUFD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsIntegrallyClosed

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
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolGermsIntegrallyClosed
theorem _root_.solution (hU : HolGermsUFD.Statement) : HolGermsIntegrallyClosed.Statement := by
  intro d y
  have := hU (Fin d) y
  exact ⟨HolGermsDomain.proof (Fin d) y, inferInstance⟩
end HolGermsIntegrallyClosed
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
