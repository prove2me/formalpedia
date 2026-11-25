-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:31.761283+00:00
-- url     : https://prove2.me/submissions/f69f728a-d526-42dd-9fb0-a2512e06776c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRankRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjMaxRankRegular
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
open GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
namespace GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ τ : Type*}
    [Fintype κ] [Fintype τ] {F : E → κ → ℂ} {u : E} (hF : DifferentiableAt ℂ F u) (a : τ → κ)
    (b : κ) (hb : F u b ≠ 0) (v : E) (t : τ) :
    fderiv ℂ (fun w t => F w (a t) / F w b) u v t =
      (F u b * fderiv ℂ F u v (a t) - F u (a t) * fderiv ℂ F u v b) / F u b ^ 2 := by
  have hc : ∀ k, HasFDerivAt (fun w => F w k)
      ((ContinuousLinearMap.proj k).comp (fderiv ℂ F u)) u :=
    fun k => hasFDerivAt_pi'.1 hF.hasFDerivAt k
  have hq : ∀ t, HasFDerivAt (fun w => F w (a t) / F w b)
      (F u (a t) • (ContinuousLinearMap.toSpanSingleton ℂ (-(F u b ^ 2)⁻¹)).comp
          ((ContinuousLinearMap.proj b).comp (fderiv ℂ F u)) +
        (F u b)⁻¹ • (ContinuousLinearMap.proj (a t)).comp (fderiv ℂ F u)) u := by
    intro t
    have h := (hc (a t)).fun_mul ((hasFDerivAt_inv hb).comp u (hc b))
    simp only [Function.comp_def] at h
    simpa only [div_eq_mul_inv] using h
  rw [(hasFDerivAt_pi.2 hq).fderiv]
  simp
  field_simp
  ring
end GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
