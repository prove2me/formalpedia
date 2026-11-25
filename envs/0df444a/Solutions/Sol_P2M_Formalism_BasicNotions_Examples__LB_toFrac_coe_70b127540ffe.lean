-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:08.033182+00:00
-- url     : https://prove2.me/submissions/33364a53-ee96-4788-93e2-82fca19ed8ef

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (a : ↥(OL LL)) : toFrac LL (a : ↥LL.1) = algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a := by
  show (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (a : ↥LL.1) = _
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
  rfl
end Formalism.BasicNotions.Examples₂.LB
