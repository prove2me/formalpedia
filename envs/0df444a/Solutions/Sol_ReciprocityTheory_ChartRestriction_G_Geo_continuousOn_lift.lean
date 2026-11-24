-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.continuousOn_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:53.711085+00:00
-- url     : https://prove2.me/submissions/cac5a379-c01c-4123-86f2-8cd41f112c7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    R.holo x p j _ ⟨(R.A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hz⟩
  have hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z :=
    ha.continuousAt.comp ((R.A.chart j).continuousAt hj)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
  simp only [Function.comp_apply, (R.A.chart j).left_inv hw]
end ReciprocityTheory.ChartRestriction.G.Geo
