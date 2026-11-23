-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:35.959486+00:00
-- url     : https://prove2.me/submissions/a19c9701-645e-4618-ab04-a5b982cbf116

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
theorem _root_.solution (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  have e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i := by
    rw [Nat.add_sub_cancel' X.p0_le]
  rw [e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha : (a : ℕ) < r := lt_of_lt_of_le a.isLt X.p0_le
    simp only [hg, dif_pos ha]
    rfl
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; have := X.p0_le; omega
    simp only [hg, dif_pos hm]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
