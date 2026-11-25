-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.quad_AtA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:55.011343+00:00
-- url     : https://prove2.me/submissions/41850cf7-00ac-4ada-8896-5f3bd2986b19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_dot_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
