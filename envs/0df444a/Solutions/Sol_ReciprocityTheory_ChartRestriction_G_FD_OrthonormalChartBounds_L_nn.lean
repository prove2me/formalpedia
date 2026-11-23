-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.L_nn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:48.518236+00:00
-- url     : https://prove2.me/submissions/cf27ef2b-759f-420c-b975-0cb742a4d338

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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    X.lowBlock Z τ (nI X m) (nI X m') = if m = m' then 1 else 0 := by
  have h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0) := by
    rw [nI_val_eq_p0_add, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : m = m'
  · subst h
    simp
  · have h1 : nI X m ≠ nI X m' := by
      intro e
      have h' := congrArg Fin.val e
      rw [nI_val_eq_p0_add, nI_val_eq_p0_add] at h'
      exact h (Fin.ext (by omega))
    rw [if_neg h, if_neg h1]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
