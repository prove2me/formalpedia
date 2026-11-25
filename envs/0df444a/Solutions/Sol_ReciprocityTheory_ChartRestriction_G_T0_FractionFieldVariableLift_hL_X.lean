-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hL_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:11.117234+00:00
-- url     : https://prove2.me/submissions/49548fd6-f2a5-40d1-8235-327adc818939

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
theorem _root_.solution (v : TVar D N) : hL K D N (MvPolynomial.X v) =
    if h : v.1 = 0 then MvPolynomial.X v.2 else MvPolynomial.C (MvPolynomial.X ⟨v, h⟩) := by
  by_cases h : v.1 = 0
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
  · simp [hL, eT, h, MvPolynomial.sumRingEquiv_C, MvPolynomial.sumRingEquiv_X_inl, MvPolynomial.sumRingEquiv_X_inr]
end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
