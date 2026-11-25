-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:29.066772+00:00
-- url     : https://prove2.me/submissions/89479e2b-d486-42ce-a3f0-d744f9e2dec4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularNull
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularNull
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegularNull
theorem _root_.solution {n : ℕ} {q : (Fin n → ℂ) → Fin n → ℂ} {u : Fin n → ℂ}
    (hq : AnalyticAt ℂ q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ q v : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) u := by
  classical
  have he : ∀ i k : Fin n, AnalyticAt ℂ (fun v => fderiv ℂ q v (Pi.single k 1) i) u := by
    intro i k
    let L : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single k 1))
    exact (L.analyticAt _).comp hq.fderiv
  have hm : (fun v => LinearMap.det (fderiv ℂ q v : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) =
      fun v => Matrix.det (Matrix.of fun i k => fderiv ℂ q v (Pi.single k 1) i) := by
    funext v
    rw [← LinearMap.det_toMatrix']
    congr 1
  rw [hm]
  simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum fun σ _ =>
    analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun i _ => he _ _)
end GroundTheory.Heights₂.Heights.Targets.ProjRegularNull
