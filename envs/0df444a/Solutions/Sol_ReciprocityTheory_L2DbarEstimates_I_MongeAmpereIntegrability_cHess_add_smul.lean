-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:59.043727+00:00
-- url     : https://prove2.me/submissions/ddcf3831-771a-4a32-b750-96a48e0e7dbf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_wd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.I
namespace MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
private theorem lin_lemma' {g₁ g₂ : V n → ℂ} {y : V n} (h₁ : DifferentiableAt ℝ g₁ y)
    (h₂ : DifferentiableAt ℝ g₂ y) (c : ℂ) (j : Fin n) :
    wd n j (fun w => g₁ w + c * g₂ w) y = wd n j g₁ y + c * wd n j g₂ y ∧
      wdb n j (fun w => g₁ w + c * g₂ w) y = wdb n j g₁ y + c * wdb n j g₂ y := by
  have hF : fderiv ℝ (fun w => g₁ w + c * g₂ w) y = fderiv ℝ g₁ y + c • fderiv ℝ g₂ y := by
    have H : HasFDerivAt (fun w => g₁ w + c * g₂ w) (fderiv ℝ g₁ y + c • fderiv ℝ g₂ y) y :=
      h₁.hasFDerivAt.add (h₂.hasFDerivAt.const_mul c)
    exact H.fderiv
  constructor <;>
    simp only [wd, wdb, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] <;> ring
end
end MongeAmpereIntegrability
end ReciprocityTheory.L2DbarEstimates.I
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution {Ω : Set (V n)} (hΩ : IsOpen Ω) {p q : V n → ℝ}
    (hp : ContDiffOn ℝ ∞ p Ω) (hq : ContDiffOn ℝ ∞ q Ω) (t : ℝ) {y : V n} (hy : y ∈ Ω) :
    cHess n (fun w => ((p w + t * q w : ℝ) : ℂ)) y =
      cHess n (fun w => (p w : ℂ)) y + (t : ℂ) • cHess n (fun w => (q w : ℂ)) y := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hP := cdo_ofReal hp
  have hQ := cdo_ofReal hq
  have dP : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (p w : ℂ)) v := fun v hv =>
    (hP.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have dQ : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (q w : ℂ)) v := fun v hv =>
    (hQ.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hfun : (fun w => ((p w + t * q w : ℝ) : ℂ)) = fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ) := by
    funext w; push_cast; ring
  rw [hfun]
  have hev : wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v := by
    filter_upwards [hΩ.mem_nhds hy] with v hv
    exact (lin_lemma' (dP v hv) (dQ v hv) _ k).2
  have e1 : wd n j (wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ))) y =
      wd n j (fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v) y := by
    simp only [wd, hev.fderiv_eq]
  rw [e1]
  have dP' : DifferentiableAt ℝ (wdb n k (fun w => (p w : ℂ))) y :=
    (((cdo_wd hΩ hP k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have dQ' : DifferentiableAt ℝ (wdb n k (fun w => (q w : ℂ))) y :=
    (((cdo_wd hΩ hQ k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  exact (lin_lemma' dP' dQ' _ j).1
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
