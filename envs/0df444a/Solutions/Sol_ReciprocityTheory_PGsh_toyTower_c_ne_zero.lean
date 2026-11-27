-- Prove2me | solution 1 for ReciprocityTheory.PGsh.toyTower_c_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:53.257863+00:00
-- url     : https://prove2.me/submissions/788095ed-4d8e-40e6-8892-d5c19d326a32

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open ReciprocityTheory ReciprocityTheory.PGsh
namespace ReciprocityTheory.PGsh
theorem _root_.solution (p : ℕ) [Fact p.Prime] : (toyTower p).c ≠ 0 := (show (1 : (ZMod p)⟦X⟧) ≠ 0 from one_ne_zero)
end ReciprocityTheory.PGsh
