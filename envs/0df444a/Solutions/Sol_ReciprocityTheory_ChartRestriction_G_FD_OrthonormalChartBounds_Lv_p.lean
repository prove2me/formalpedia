-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Lv_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:29.367848+00:00
-- url     : https://prove2.me/submissions/e0fd4948-86d0-4a5b-ba77-0273790f86d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight

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
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (a : Fin X.p0) :
    ∑ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j * v j = v (Fin.castLE X.p0_le a) := by
  have hL : ∀ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j =
      if Fin.castLE X.p0_le a = j then 1 else 0 := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [dif_neg (fun hh => absurd hh.1 (not_le.mpr (by simp))), add_zero]
  simp only [hL, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
