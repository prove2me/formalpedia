-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.isotropic_outside_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:52.522882+00:00
-- url     : https://prove2.me/submissions/b5bebe83-e0bc-4bee-85c3-dc33deba278c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLineOfCovering
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_isotropic_outside_line_of_covering
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integerApproximationCount_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds
end ReciprocityTheory.ChartRestriction.G.FD
