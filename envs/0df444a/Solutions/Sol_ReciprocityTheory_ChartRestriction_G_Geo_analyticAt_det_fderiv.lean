-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_det_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:11.144131+00:00
-- url     : https://prove2.me/submissions/fdc805a5-1d2c-4da6-b6fa-9fac44ed5d1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL

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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {Q : (Fin e → ℂ) → (Fin e → ℂ)} {u : Fin e → ℂ}
    (hQ : AnalyticAt ℂ Q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) u := by
  have hF : AnalyticAt ℂ (fderiv ℂ Q) u := hQ.fderiv

  have hentry : ∀ i j : Fin e, AnalyticAt ℂ
      (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) u := by
    intro i j
    have hL : AnalyticAt ℂ (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L (Pi.single j 1) i)
        (fderiv ℂ Q u) := by
      have h := ContinuousLinearMap.analyticAt
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).comp
          (ContinuousLinearMap.apply ℂ (Fin e → ℂ) (Pi.single j (1 : ℂ)))) (fderiv ℂ Q u)
      exact h
    have heq : (fun v => LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) i j) =
        fun v => fderiv ℂ Q v (Pi.single j 1) i := by
      funext v
      rw [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [heq]
    exact hL.comp hF

  have hdet : (fun v => LinearMap.det (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) =
      fun v => (LinearMap.toMatrix' (fderiv ℂ Q v : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))).det := by
    funext v
    rw [LinearMap.det_toMatrix']
  rw [hdet]
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hentry _ _)
end ReciprocityTheory.ChartRestriction.G.Geo
