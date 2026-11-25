-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.hess_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:23:56.54627+00:00
-- url     : https://prove2.me/submissions/14936974-a289-481e-adf1-a1634a47bc73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fderiv_re_apply

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
open MvPolynomial Filter Topology
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {G : (Fin e → ℂ) → ℂ} {y : Fin e → ℂ} (hG : AnalyticAt ℂ G y) (v w : Fin e → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => (G y').re)) y v w = (fderiv ℂ (fderiv ℂ G) y v w).re := by
  let Φ : ((Fin e → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin e → ℂ) ℂ ℝ ℝ)
  have hΦ : ∀ L : (Fin e → ℂ) →L[ℂ] ℂ, ∀ u, Φ L u = (L u).re := fun L u => rfl
  have heq : fderiv ℝ (fun y' => (G y').re) =ᶠ[𝓝 y] fun y' => Φ (fderiv ℂ G y') := by
    filter_upwards [hG.eventually_analyticAt] with y' hy'
    ext u
    rw [fderiv_re_apply hy'.differentiableAt u, hΦ]
  have hD : HasFDerivAt (fderiv ℂ G) (fderiv ℂ (fderiv ℂ G) y) y :=
    hG.fderiv.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Φ (fderiv ℂ G y'))
      (Φ.comp ((fderiv ℂ (fderiv ℂ G) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hD.restrictScalars ℝ)
  rw [heq.fderiv_eq, h2.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo
