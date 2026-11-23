-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Gp_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:45.63629+00:00
-- url     : https://prove2.me/submissions/fe6f83ee-6360-41fd-8f55-391ca32b5a26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NsqMulVecLeOpN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_L_pp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_L_np
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sgn_p
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sgn_n
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Gp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_eq_sum_castLE_add_sum_nI (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) :=
  sum_split X f
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    Gp X Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) =
      (if a = c then 1 else 0) - ∑ m, Z τ m a * conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_np X, sgn_p X, sgn_n X]
  by_cases hac : a = c
  · subst hac
    simp [sub_eq_add_neg]
  · simp [hac, Ne.symm hac, sub_eq_add_neg]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
