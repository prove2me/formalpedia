-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.smooth_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:21.550139+00:00
-- url     : https://prove2.me/submissions/702ce21a-5caa-4553-b711-ec653bf56963

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_h_eq_of_sameOrbit
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
theorem _root_.solution (R : AnLogRes P J e) {B : HermLine ι} (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    R.A.Smooth (fun x => Real.log (B.h (R.lift x x))) := by
  intro j
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  have hyt : y ∈ (R.A.chart j).target := hy.1
  refine ⟨(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y),
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _), ⟨hyt, R.mem_U _⟩, ?_⟩
  have hc := contDiffOn_potOf R hB ((R.A.chart j).symm y) j
  refine (hc.mono Set.inter_subset_right).congr fun y' hy' => ?_
  change Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨R.mem_U _, hy'.2.2⟩)]
end ReciprocityTheory.ChartRestriction.G.Geo
