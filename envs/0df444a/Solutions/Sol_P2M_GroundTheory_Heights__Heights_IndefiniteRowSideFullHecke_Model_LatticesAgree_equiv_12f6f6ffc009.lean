-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_LatticesAgree_equiv_12f6f6ffc009
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:00:22.321969+00:00
-- url     : https://prove2.me/submissions/74822352-5853-43fa-851d-fe24a8ac761e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace LatticesAgree
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.LatticesAgree.Statement ↔ LatticesAgree.Statement := by
  constructor
  · intro h A K V _ _ _ _ _ _ _ _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp => ?_
    exact SetLike.coe_injective (hloc p.asIdeal p.isPrime hp)
  · intro h A _ _ _ _ K _ _ _ V _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp hh => ?_
    have e := hloc ⟨p, hp⟩ hh
    exact congrArg (fun P : Submodule A V => (P : Set V)) e
end LatticesAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
