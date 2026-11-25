-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_absNorm_eq_index_aad97d015a0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:17.198746+00:00
-- url     : https://prove2.me/submissions/89837cc0-1b1a-4ffc-bdb2-36ab4975c38d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.IdealIndexPlaces
namespace GroundTheory.Heights₂.Heights.IdealIndexPlaces
theorem _root_.solution {L : Type*} [Field L] [NumberField L] (A : Ideal (𝓞 L)) :
    A.absNorm = A.toAddSubgroup.index := rfl
end GroundTheory.Heights₂.Heights.IdealIndexPlaces
