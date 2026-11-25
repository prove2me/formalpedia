-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.fs_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:07.450753+00:00
-- url     : https://prove2.me/submissions/192c577c-d21a-4f19-91aa-64aa171f5190

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_comp_finiteCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (ζ0 : ℂ) (h0 : ζ0 ≠ 0) : ∃ W : Set (OnePoint ℂ), IsOpen W ∧
    (ζ0 : OnePoint ℂ) ∈ W ∧ ∃ G : OnePoint ℂ → ℂ, p1.HoloOn W G ∧
      ∀ z ∈ W, ∃ ζ : ℂ, z = ζ ∧ ζ ≠ 0 ∧ (G z).re = Real.log ‖ζ‖ := by
  set B : Set ℂ := {ζ | ζ * ζ0⁻¹ ∈ Complex.slitPlane} with hBdef
  have hBo : IsOpen B := Complex.isOpen_slitPlane.preimage (continuous_id.mul continuous_const)
  have hF : AnalyticOnNhd ℂ (fun ζ : ℂ => Complex.log (ζ * ζ0⁻¹) + (Real.log ‖ζ0‖ : ℂ)) B := by
    intro ζ hζ
    exact ((analyticAt_id.mul analyticAt_const).clog hζ).add analyticAt_const
  refine ⟨projectiveLineChartAtZero.source ∩ projectiveLineChartAtZero ⁻¹' {w | w 0 ∈ B},
    projectiveLineChartAtZero.isOpen_inter_preimage (hBo.preimage (continuous_apply 0)), ⟨⟨ζ0, rfl⟩, ?_⟩, _,
    holomorphicOn_comp_finiteCoord hF, ?_⟩
  · show ζ0 * ζ0⁻¹ ∈ Complex.slitPlane
    rw [mul_inv_cancel₀ h0]
    exact Complex.one_mem_slitPlane
  · rintro z ⟨⟨ζ, rfl⟩, hz⟩
    have hζB : ζ * ζ0⁻¹ ∈ Complex.slitPlane := hz
    have hne : ζ * ζ0⁻¹ ≠ 0 := Complex.slitPlane_ne_zero hζB
    have hζ : ζ ≠ 0 := left_ne_zero_of_mul hne
    refine ⟨ζ, rfl, hζ, ?_⟩
    show (Complex.log (crd0 (ζ : OnePoint ℂ) * ζ0⁻¹) + (Real.log ‖ζ0‖ : ℂ)).re = Real.log ‖ζ‖
    rw [finiteCoord_coe, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_mul, norm_inv,
      Real.log_mul (norm_ne_zero_iff.2 hζ) (inv_ne_zero (norm_ne_zero_iff.2 h0)), Real.log_inv]
    ring
end ReciprocityTheory.AnForm.M
