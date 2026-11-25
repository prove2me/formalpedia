-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mj_xZ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:32.352804+00:00
-- url     : https://prove2.me/submissions/6bd15e7b-4171-4979-8049-481f3254fcb4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealLower2

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
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show (mat x τ * X.lowBlock 0 τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [h1, Matrix.mul_one]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
