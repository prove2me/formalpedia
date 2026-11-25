-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold.c_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:16.487992+00:00
-- url     : https://prove2.me/submissions/0413d245-9bd5-4ae8-b354-53a973501e9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
theorem _root_.solution (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  positivity
end ReciprocityTheory.ChartRestriction.G.FD.IsotropicThreshold
