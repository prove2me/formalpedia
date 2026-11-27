-- Prove2me | solution 1 for ReciprocityTheory.PGsh.toyTower_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:59.321076+00:00
-- url     : https://prove2.me/submissions/e0650cfd-646f-4116-af69-ea3230eba405

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] : IsDomain ((toyTower p).O : Type) := (inferInstance : IsDomain (ZMod p)⟦X⟧)
end ReciprocityTheory.PGsh
