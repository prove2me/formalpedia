-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.fourier_coefficients_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:45.152102+00:00
-- url     : https://prove2.me/submissions/cd059cfb-b033-4a80-ad85-0de1efc81fc8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_fourier_coefficients_of_vector_group
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_unipotent_vector_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : FourierCoefficientProperties (E := E) :=
  fourier_coefficients_of_vector_group unipotent_vector_group
end ReciprocityTheory.ChartRestriction.G.FD
