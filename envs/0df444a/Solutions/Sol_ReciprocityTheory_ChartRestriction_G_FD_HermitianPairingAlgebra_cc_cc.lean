-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.cc_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:39.898706+00:00
-- url     : https://prove2.me/submissions/3541374f-d375-482e-92bb-ce840d6a3be1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
theorem _root_.solution (a : E) : cc (cc a) = a := by
  exact IsCMField.complexConj_apply_apply E a
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
