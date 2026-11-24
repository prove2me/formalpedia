-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:50.63306+00:00
-- url     : https://prove2.me/submissions/e6b2d6d7-2637-47e6-a6b8-cbda57e80d4f

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
theorem _root_.solution {α : Type*} (s : Finset α) (y : α → ℝ) {Y : ℝ} (hy : ∀ i ∈ s, |y i| ≤ Y) :
    |∏ i ∈ s, y i| ≤ Y ^ s.card := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |y i| ≤ ∏ _i ∈ s, Y := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hy
    _ = Y ^ s.card := Finset.prod_const Y
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
