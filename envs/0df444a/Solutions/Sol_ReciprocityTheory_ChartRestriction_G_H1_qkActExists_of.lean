-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.qkActExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:38:46.479922+00:00
-- url     : https://prove2.me/submissions/85a249be-4f46-4ba3-8dd7-166fb6bab57d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_QkActPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_qkAct_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (hG : Out.GlobalFnsSt) : QkActExistsStatement := by
  intro E _ _ _ H V _ _ _ t P
  letI := H.starRing
  intro F _ _ _ k a p
  exact Geo.Tor.qkAct_exists hG P.D.tau_bimult P.oD a p
end ReciprocityTheory.ChartRestriction.G.H1
