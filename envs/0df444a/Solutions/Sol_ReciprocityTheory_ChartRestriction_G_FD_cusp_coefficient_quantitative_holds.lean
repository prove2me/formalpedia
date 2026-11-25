-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.cusp_coefficient_quantitative_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:49.0067+00:00
-- url     : https://prove2.me/submissions/05c5ca06-0dd7-425b-8fe8-c9cd9da3d374

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientQuantitative
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientQuantitativeHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientQuantitative_cusp_coefficient_bound_of_unipotent_lattice_lift
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
theorem _root_.solution : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift
end ReciprocityTheory.ChartRestriction.G.FD
