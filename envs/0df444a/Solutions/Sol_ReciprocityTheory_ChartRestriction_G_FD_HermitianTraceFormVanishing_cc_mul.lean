-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:50.594299+00:00
-- url     : https://prove2.me/submissions/4f3898a0-d01b-49a6-90bc-431e021f07ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
theorem _root_.solution (a b : E) : cc (a * b) = cc a * cc b := by simp [cc]
end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
