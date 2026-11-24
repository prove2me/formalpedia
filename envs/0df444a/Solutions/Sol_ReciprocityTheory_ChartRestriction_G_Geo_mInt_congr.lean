-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:56.115571+00:00
-- url     : https://prove2.me/submissions/89546763-78d9-41f0-95ad-3cbe3170f648

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Φ' : Fin e → LocPot X} {g g' : X → ℝ}
    (hΦ : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Φ' j y)
    (hg : ∀ x, g x = g' x) : mInt A Φ g = mInt A Φ' g' := by
  unfold ReciprocityTheory.AnForm.M.mInt
  by_cases h : Nonempty (ChartPartition A)
  · rw [dif_pos h, dif_pos h]
    unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [hg, hΦ j y hy]
  · rw [dif_neg h, dif_neg h]
end ReciprocityTheory.ChartRestriction.G.Geo
