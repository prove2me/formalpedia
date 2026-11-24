-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:43.033656+00:00
-- url     : https://prove2.me/submissions/07217ad9-7b80-45e7-a55f-f5e51219b585

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
theorem _root_.solution {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm B.inv := (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} from hB).inv
  fun z hz => (B.pos z hz).ne'
end ReciprocityTheory.ChartRestriction.G.Geo
