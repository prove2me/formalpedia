-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.L_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:05.488784+00:00
-- url     : https://prove2.me/submissions/20df44f3-9b0b-4b30-a1bd-4cb02cf6cf23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NsqMulVecLeOpN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock

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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) = if a = c then 1 else 0 := by
  have ha := a.isLt
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0) := by
    simp only [Fin.val_castLE]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : a = c
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
