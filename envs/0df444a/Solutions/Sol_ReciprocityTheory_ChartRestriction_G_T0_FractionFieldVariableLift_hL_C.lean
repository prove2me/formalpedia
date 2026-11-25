-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hL_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:08.779723+00:00
-- url     : https://prove2.me/submissions/b125ab23-a2e0-49a5-9aa3-2e9650249d45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
open ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
theorem _root_.solution (r : K) : hL K D N (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [hL, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
