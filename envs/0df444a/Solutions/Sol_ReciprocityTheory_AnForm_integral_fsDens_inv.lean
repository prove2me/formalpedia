-- Prove2me | solution 1 for ReciprocityTheory.AnForm.integral_fsDens_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:51.233859+00:00
-- url     : https://prove2.me/submissions/3f93b357-88f9-40b3-ac17-03af59d85cc1

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution (g : ℂ → ℝ) :
    ∫ z, g z⁻¹ * fsDens z = ∫ z, g z * fsDens z := by
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have himg : (fun z : ℂ => z⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hz; exact ⟨z⁻¹, by simpa using hz, inv_inv z⟩
  have hder : ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivWithinAt (fun z : ℂ => z⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars ℝ)
      ({0}ᶜ) z := by
    intro z hz
    exact ((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hder
    inv_injective.injOn (fun z => g z * fsDens z)
  rw [himg] at hcv
  have hnull : ∀ F : ℂ → ℝ, ∫ z in ({0}ᶜ : Set ℂ), F z = ∫ z, F z := fun F => by
    rw [restrict_compl_singleton]
  rw [hnull, hnull] at hcv
  rw [hcv]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz
  have hz0 : z ≠ 0 := hz
  have hdet : (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars
      ℝ).det = ‖z‖⁻¹ ^ 4 := by
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
      Complex.normSq_eq_norm_sq, ← pow_mul]
  rw [hdet, smul_eq_mul, fsDens, fsDens, norm_inv]
  have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have := Real.pi_pos
  rw [abs_of_nonneg (by positivity)]
  field_simp
  ring
end ReciprocityTheory.AnForm
