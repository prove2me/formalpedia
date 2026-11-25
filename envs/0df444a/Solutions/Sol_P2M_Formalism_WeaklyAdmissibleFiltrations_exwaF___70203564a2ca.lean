-- Prove2me | solution 1 for P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:04.545137+00:00
-- url     : https://prove2.me/submissions/bd5c108d-89b7-4dfb-a9b9-7f129b7a33c1

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (c : LL) (hc : c ≠ 0) (x : ZMod n → LL) : (exwaF c hc).φ x = exwaPhi c hc x := rfl
end Formalism.WeaklyAdmissibleFiltrations
