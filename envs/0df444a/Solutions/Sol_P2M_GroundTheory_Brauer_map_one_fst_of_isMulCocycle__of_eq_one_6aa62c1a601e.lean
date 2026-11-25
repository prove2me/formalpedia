-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:37.071477+00:00
-- url     : https://prove2.me/submissions/8d68c786-f7d8-46d6-baef-e7629b78b408

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints

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
namespace GroundTheory.Brauer
theorem _root_.solution {f : G × G → M} (hf : IsMulCocycle₂ f)
    (h1 : f (1, 1) = 1) (g : G) : f (1, g) = 1 := by
  rw [map_one_fst_of_isMulCocycle₂ hf, h1]
end GroundTheory.Brauer
