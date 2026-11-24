-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.potOf_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:35.979242+00:00
-- url     : https://prove2.me/submissions/6e0c2cb8-b6de-4db1-b7a3-d12c005fa941

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_h_eq_of_sameOrbit

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
theorem _root_.solution (R : AnLogRes P J e) {B : HermLine ι} (hB0 : B.a = 0) (j : Fin R.A.n)
    (y : Fin e → ℂ) (hy : y ∈ (R.A.chart j).target) :
    (fun y' => (potOf R B).φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (LocPot.ofFun fun x => Real.log (B.h (R.lift x x))).φ ((R.A.chart j).symm y)
        ((R.A.chart j).symm y') := by
  have hev : ∀ᶠ y' in 𝓝 y, (R.A.chart j).symm y' ∈ R.U ((R.A.chart j).symm y) :=
    ((R.A.chart j).continuousAt_symm hy).preimage_mem_nhds
      ((R.isOpen_U _).mem_nhds (R.mem_U _))
  filter_upwards [hev] with y' hy'
  change Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨hy', R.mem_U _⟩)]
end ReciprocityTheory.ChartRestriction.G.Geo
