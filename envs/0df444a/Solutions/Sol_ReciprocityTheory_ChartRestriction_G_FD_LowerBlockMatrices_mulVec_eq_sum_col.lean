-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.mulVec_eq_sum_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:10.910891+00:00
-- url     : https://prove2.me/submissions/3eb0de6d-d1e1-4277-87eb-ede9c1403cd2

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
theorem _root_.solution (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) : M *ᵥ w = ∑ c, w c • col M c := by
  funext k
  simp only [Matrix.mulVec, dotProduct, col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ ↦ mul_comm _ _
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
