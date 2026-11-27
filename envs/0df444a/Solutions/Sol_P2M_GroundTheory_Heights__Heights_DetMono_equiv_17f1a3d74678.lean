-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DetMono_equiv_17f1a3d74678
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:41.523389+00:00
-- url     : https://prove2.me/submissions/66ae0612-14d7-4640-82fa-b42d97e62a46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Imports

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
namespace GroundTheory.Heights₂.Heights
namespace DetMono
theorem _root_.solution :
    FourB.HermitianDetMono.Statement ↔ IndefiniteRowSideFullHecke.FourB.DetMono.Statement := by
  constructor
  · intro h n A A' hA
    exact h n A A' hA.1 hA.2
  · intro h n A B hB hAB
    exact h n A B ⟨hB, hAB⟩
end DetMono
end GroundTheory.Heights₂.Heights
