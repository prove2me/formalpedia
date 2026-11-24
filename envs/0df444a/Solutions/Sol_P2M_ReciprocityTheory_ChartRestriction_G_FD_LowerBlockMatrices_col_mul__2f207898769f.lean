-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:10.255024+00:00
-- url     : https://prove2.me/submissions/d4b7af1c-8fe3-4fb3-9bf0-7ef21fc5edab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
theorem _root_.solution (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * B) a = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col B a := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
