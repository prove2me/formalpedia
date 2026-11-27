-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TX.flagDomainConj_hostXi_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:22.386813+00:00
-- url     : https://prove2.me/submissions/30600e35-89e6-48f0-811e-b9b09431e440

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.TX
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.I2.TX
theorem _root_.solution : cc X.ξ0 = -X.ξ0 := X.ξ0_im
end ReciprocityTheory.ChartRestriction.G.I2.TX
