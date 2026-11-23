-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:43.919392+00:00
-- url     : https://prove2.me/submissions/74323ac6-1714-4b2b-9f71-fbdd9836c0da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
theorem _root_.solution (a : E) : cc (cc a) = a := by simp [cc]
end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
