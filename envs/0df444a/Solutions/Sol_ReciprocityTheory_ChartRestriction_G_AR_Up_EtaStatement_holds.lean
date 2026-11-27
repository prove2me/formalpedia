-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.EtaStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:38:23.006976+00:00
-- url     : https://prove2.me/submissions/6bcc5a75-3b79-42d7-9909-66e5b4c191a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_EtaStatementHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_EtaPf_eta_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) :=
  EtaPf.eta_holds
end ReciprocityTheory.ChartRestriction.G.AR.Up
