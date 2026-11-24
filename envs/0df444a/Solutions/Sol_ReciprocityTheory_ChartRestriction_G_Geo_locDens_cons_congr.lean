-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.locDens_cons_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:24.551891+00:00
-- url     : https://prove2.me/submissions/18418dee-497e-4d54-b828-e1d11d5b9dcf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDens_congr

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
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    {Q Q' : LocPot X} (Φ : Fin e → LocPot X)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y'))
      =ᶠ[𝓝 y] fun y' => Q'.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    ∀ j, ∀ y ∈ (A.chart j).target,
      locDens A (Fin.cons Q Φ) j y = locDens A (Fin.cons Q' Φ) j y := by
  intro j y hy
  unfold ReciprocityTheory.AnForm.M.locDens
  apply maDens_congr
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact h j y hy
  | succ i =>
    simp only [Fin.cons_succ]
    exact Filter.EventuallyEq.rfl
end ReciprocityTheory.ChartRestriction.G.Geo
