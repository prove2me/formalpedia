-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_segre_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:00.375677+00:00
-- url     : https://prove2.me/submissions/4730ce2c-0cd1-4061-a562-9fce532ecdc4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_lift_chart

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hseg : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u := by
    rw [analyticAt_pi_iff]
    intro i
    simp only [segre]
    have hp := Finset.analyticAt_prod (Finset.univ : Finset K) fun k _ => (analyticAt_pi_iff.mp hl) ⟨k, i k⟩
    exact hp.congr (Filter.Eventually.of_forall fun v => by simp [Finset.prod_apply])
  have := ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hseg
  exact this
end ReciprocityTheory.ChartRestriction.G.Geo
