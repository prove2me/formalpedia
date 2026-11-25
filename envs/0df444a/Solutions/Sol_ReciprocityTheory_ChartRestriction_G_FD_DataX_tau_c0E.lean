-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.tau_c0E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:39.927011+00:00
-- url     : https://prove2.me/submissions/21788e8e-1368-422b-af5a-3155c024df7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (τ : E →+* ℂ) : τ X.c0E = ((((X.g * dEnat E : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
  unfold c0E
  rw [map_div₀, map_natCast, map_ofNat]
  push_cast
  try ring
end ReciprocityTheory.ChartRestriction.G.FD.DataX
