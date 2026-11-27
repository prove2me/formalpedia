-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.smoothOn_potOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:10.664799+00:00
-- url     : https://prove2.me/submissions/8d0c9093-4a3b-4fb2-b1e0-77c739af7d3d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_contDiffOn_potOf

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
variable {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := fun j => contDiffOn_potOf R hL x j
end ReciprocityTheory.ChartRestriction.G.Geo
