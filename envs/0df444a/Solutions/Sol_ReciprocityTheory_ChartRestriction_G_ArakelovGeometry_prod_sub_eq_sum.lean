-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_sub_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:47.970452+00:00
-- url     : https://prove2.me/submissions/0b29bb2e-3350-492b-9e22-c23d78f1768b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) :
    ∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) =
      ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j := by
  have h := Finset.prod_add_ordered s y (fun i => -ε i)
  simp only [← sub_eq_add_neg] at h
  rw [h]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
