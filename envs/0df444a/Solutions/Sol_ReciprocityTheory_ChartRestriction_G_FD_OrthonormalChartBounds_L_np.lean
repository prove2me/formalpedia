-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.L_np
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:48.831272+00:00
-- url     : https://prove2.me/submissions/b2b10947-73e6-41c3-b25a-0028f112c165

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
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma nI_val_eq_p0_add (m : Fin (r - X.p0)) : ((nI X m : Fin r) : ℕ) = X.p0 + m := rfl
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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    X.lowBlock Z τ (nI X m) (Fin.castLE X.p0_le c) = Z τ m c := by
  have hc := c.isLt
  have h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r) := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
