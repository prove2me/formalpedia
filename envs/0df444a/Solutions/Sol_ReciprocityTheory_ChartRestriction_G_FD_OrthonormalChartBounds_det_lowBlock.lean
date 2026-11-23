-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.det_lowBlock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:06.039369+00:00
-- url     : https://prove2.me/submissions/e5257a91-c5fd-4a58-80f2-7cec711cfce4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dif_neg (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dif_neg]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
