-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:39.498022+00:00
-- url     : https://prove2.me/submissions/f5db34a9-0521-4fee-902a-5f239261c8b1

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
    (h1 : f (1, 1) = 1) (g : G) : f (g, 1) = 1 := by
  rw [map_one_snd_of_isMulCocycle₂ hf, h1, smul_one]
end GroundTheory.Brauer
