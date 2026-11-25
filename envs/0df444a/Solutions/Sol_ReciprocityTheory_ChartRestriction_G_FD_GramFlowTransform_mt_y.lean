-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.mt_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:56.198744+00:00
-- url     : https://prove2.me/submissions/0c9a78b0-7f08-4083-88cc-75937fc3e011

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}
namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
theorem _root_.solution {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) :
    GramDeterminantReal.mt τ G f e = ∑ b, yv τ G f e b * conj (cv τ G f e b) := by
  simp only [GramDeterminantReal.mt, GramDeterminantReal.yv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
