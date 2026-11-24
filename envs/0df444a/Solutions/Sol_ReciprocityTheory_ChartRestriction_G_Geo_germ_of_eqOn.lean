-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.germ_of_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:35.591374+00:00
-- url     : https://prove2.me/submissions/d4301f1f-e641-48f4-8725-567fc91256cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF

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
theorem _root_.solution (R : AnLogRes P J e) {Q Q' : LocPot R.X}
    (h : ∀ x, ∀ y ∈ R.U x, Q.φ x y = Q'.φ x y) (j : Fin R.A.n) (y : Fin e → ℂ)
    (hy : y ∈ (R.A.chart j).target) :
    (fun y' => Q.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q'.φ ((R.A.chart j).symm y) ((R.A.chart j).symm y') := by
  have hc : ContinuousAt (R.A.chart j).symm y := (R.A.chart j).continuousAt_symm hy
  have hU : R.U ((R.A.chart j).symm y) ∈ 𝓝 ((R.A.chart j).symm y) :=
    (R.isOpen_U _).mem_nhds (R.mem_U _)
  filter_upwards [hc hU] with y' hy'
  exact h _ _ hy'
end ReciprocityTheory.ChartRestriction.G.Geo
