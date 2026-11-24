-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.h_eq_of_sameOrbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.413166+00:00
-- url     : https://prove2.me/submissions/eacc61b1-4ec9-4457-b36e-eb30ad9c7580

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
theorem _root_.solution {B : HermLine ι} (hB : B.a = 0) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp
end ReciprocityTheory.ChartRestriction.G.Geo
