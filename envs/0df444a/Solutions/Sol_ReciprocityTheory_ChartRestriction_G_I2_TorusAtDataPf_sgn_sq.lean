-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sgn_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:11.662196+00:00
-- url     : https://prove2.me/submissions/eeea77e2-0d62-4bd6-a57e-fe17dc8a0d5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution (a : Fin r) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> push_cast <;> norm_num
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
