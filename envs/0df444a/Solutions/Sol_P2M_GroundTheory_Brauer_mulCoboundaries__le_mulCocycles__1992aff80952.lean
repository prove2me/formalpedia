-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_mulCoboundaries__le_mulCocycles__1992aff80952
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:21.79461+00:00
-- url     : https://prove2.me/submissions/d778de9e-3e61-4766-8b13-418780b7e42d

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_P2M_GroundTheory_Brauer_isMulCocycle__of_isMulCoboundary__1fe17ff20d13

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}
variable (G M)
namespace GroundTheory.Brauer
theorem _root_.solution : mulCoboundaries₂ G M ≤ mulCocycles₂ G M :=
  fun _ hf => isMulCocycle₂_of_isMulCoboundary₂ hf
end GroundTheory.Brauer
