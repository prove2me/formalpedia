-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.locDens_congr_of_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:24.063191+00:00
-- url     : https://prove2.me/submissions/9a105b0d-b10d-4b3c-93df-bd7cad76f432

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDens_congr_fderiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_germ_of_eqOn

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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) {Φ Φ' : Fin e → LocPot R.X}
    (h : ∀ i x, ∀ y ∈ R.U x, (Φ i).φ x y = (Φ' i).φ x y) :
    ∀ j, ∀ y ∈ (R.A.chart j).target, locDens R.A Φ j y = locDens R.A Φ' j y := by
  intro j y hy
  unfold locDens
  apply maDens_congr_fderiv
  intro i
  exact (germ_of_eqOn R (h i) j y hy).fderiv
end ReciprocityTheory.ChartRestriction.G.Geo
