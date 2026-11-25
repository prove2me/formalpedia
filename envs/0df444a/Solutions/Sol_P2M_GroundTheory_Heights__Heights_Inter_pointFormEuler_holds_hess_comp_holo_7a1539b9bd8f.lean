-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_hess_comp_holo_7a1539b9bd8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:05.471612+00:00
-- url     : https://prove2.me/submissions/6f92a754-d81d-4046-9294-0efb43aa013a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution {φ : ((Σ k, ι k) → ℂ) → ℝ} {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F y)) (hF : AnalyticAt ℂ F y) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fderiv ℝ φ) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ φ (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) := by
  have hψ : ContDiffAt ℝ 2 (fun y' => φ (F y')) y := hφ.comp y (hF.contDiffAt.restrict_scalars ℝ)
  have hψ1 : DifferentiableAt ℝ (fderiv ℝ (fun y' => φ (F y'))) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφev : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 φ (F y') :=
    hF.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hFev := hF.eventually_analyticAt
  have hcw : fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) y u := by
    rw [fderiv_clm_apply hψ1 (differentiableAt_const v)]
    simp
  have hev : (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ (F y') (fderiv ℂ F y' v) := by
    filter_upwards [hφev, hFev] with y' h1 h2
    rw [fderiv_fun_comp y' (h1.differentiableAt (by norm_num)) (h2.differentiableAt.restrictScalars ℝ),
      h2.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (F y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (F y')) y :=
    hd1.comp y (hF.differentiableAt.restrictScalars ℝ)
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' v) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const v)
  rw [hcw, hev.fderiv_eq, fderiv_clm_apply hc (hG.restrictScalars ℝ),
    fderiv_fun_comp y hd1 (hF.differentiableAt.restrictScalars ℝ),
    hG.fderiv_restrictScalars ℝ, hF.differentiableAt.fderiv_restrictScalars ℝ]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars']
  ring
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
