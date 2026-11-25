-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:17.985048+00:00
-- url     : https://prove2.me/submissions/66593d2c-4b17-4fe9-8d68-1801ce9c0e68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
theorem _root_.solution {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) (h0 : F u 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((F u 0 ^ 2)⁻¹) ^ n * (projNumMat F u).det := by
  classical
  have hc : ∀ i, AnalyticAt ℂ (fun v => F v i) u := fun i => analyticAt_pi_iff.1 hF i
  have key : ∀ (i : Fin n) (w : Fin n → ℂ),
      F u 0 ^ 2 * fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        F u 0 * fderiv ℂ (fun v => F v i.succ) u w - F u i.succ * fderiv ℂ (fun v => F v 0) u w := by
    intro i w
    have hq : AnalyticAt ℂ (fun v => F v i.succ / F v 0) u := (hc _).div (hc 0) h0
    have hev : (fun v => F v i.succ / F v 0 * F v 0) =ᶠ[𝓝 u] (fun v => F v i.succ) := by
      filter_upwards [(hc 0).continuousAt.eventually_ne h0] with v hv
      exact div_mul_cancel₀ _ hv
    have hmul : fderiv ℂ (fun v => F v i.succ) u = (F u i.succ / F u 0) • fderiv ℂ (fun v => F v 0) u +
        F u 0 • fderiv ℂ (fun v => F v i.succ / F v 0) u := by
      rw [← hev.fderiv_eq]
      exact fderiv_fun_mul hq.differentiableAt (hc 0).differentiableAt
    have hcomp : fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u w i =
        fderiv ℂ (fun v => F v i.succ / F v 0) u w := by
      rw [fderiv_pi (φ := fun (i : Fin n) v => F v i.succ / F v 0)
        (fun i => ((hc _).div (hc 0) h0).differentiableAt)]
      rfl
    rw [hcomp, hmul]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hM : LinearMap.toMatrix' (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = (F u 0 ^ 2)⁻¹ • projNumMat F u := by
    ext i l
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, Matrix.smul_apply,
      smul_eq_mul, projNumMat]
    rw [← key i (Pi.single l 1)]
    field_simp
  rw [← LinearMap.det_toMatrix', hM, Matrix.det_smul, Fintype.card_fin]
end GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen
