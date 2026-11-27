-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.dvrDataAt_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:25:41.931284+00:00
-- url     : https://prove2.me/submissions/fc985c33-9768-48f5-960b-fe4185c805b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrAll
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_dvrData_of_splitting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_splitsAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hC : Out.CubePullSt) (hU : Out.UnramExtSt) (hB : Out.GtBaseChangeSt) (hS : Y.SplitFibres)
    (h3 : Y.N3) (P : ValPt Y) : DvrDataAt P :=
  dvrData_of_splitting h3 P (splitsAt hC hU hB hS P)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
