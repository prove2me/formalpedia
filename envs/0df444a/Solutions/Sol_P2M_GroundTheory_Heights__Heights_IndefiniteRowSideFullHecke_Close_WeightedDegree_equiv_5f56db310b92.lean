-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_WeightedDegree_equiv_5f56db310b92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:02.117459+00:00
-- url     : https://prove2.me/submissions/8ffb1fd4-8b7b-4ba0-9485-b15363d7c292

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace WeightedDegree
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.WeightedDegree.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.WeightedDegree.Statement := by
  constructor
  · intro h ι _ _ n P D hD a p hp
    have := Fact.mk hp
    exact h ι n P D hD a p
  · intro h ι _ _ n P D hD a p hp
    exact h ι n P D hD a p hp.out
end WeightedDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
