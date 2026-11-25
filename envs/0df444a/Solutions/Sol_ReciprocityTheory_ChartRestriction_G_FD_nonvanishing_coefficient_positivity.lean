-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.nonvanishing_coefficient_positivity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:29:41.794272+00:00
-- url     : https://prove2.me/submissions/846d1139-2dcc-4266-959f-621450b67e8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingCoefficientPositivity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CoefficientPositivity_nonvanishing_coefficient_positivity_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_fourier_coefficients_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_unipotent_lattice_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : NonvanishingCoefficientPositivity (E := E) := CoefficientPositivity.nonvanishing_coefficient_positivity_of unipotent_lattice_lift fourier_coefficients_holds
end ReciprocityTheory.ChartRestriction.G.FD
