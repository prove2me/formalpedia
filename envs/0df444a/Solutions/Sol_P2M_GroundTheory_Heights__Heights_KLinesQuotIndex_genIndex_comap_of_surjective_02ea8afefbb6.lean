-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_genIndex_comap_of_surjective_02ea8afefbb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:19.242235+00:00
-- url     : https://prove2.me/submissions/43eea51b-51ea-4753-8296-7e96afd1d5c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex

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
open GroundTheory.Heights₂.Heights.KLinesQuotIndex
namespace GroundTheory.Heights₂.Heights.KLinesQuotIndex
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Surjective f) (H H' : AddSubgroup G') :
    genIndex (H.comap f) (H'.comap f) = genIndex H H' := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]
end GroundTheory.Heights₂.Heights.KLinesQuotIndex
