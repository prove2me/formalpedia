-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.cc_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:12.285926+00:00
-- url     : https://prove2.me/submissions/5a75f041-67ad-416c-9716-6204753ae42f

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
theorem _root_.solution (a b : E) : cc (a * b) = cc a * cc b := by
  exact map_mul (IsCMField.complexConj E) a b
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
