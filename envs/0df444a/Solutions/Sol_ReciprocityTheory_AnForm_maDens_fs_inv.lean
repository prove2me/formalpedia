-- Prove2me | solution 1 for ReciprocityTheory.AnForm.maDens_fs_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:53.162796+00:00
-- url     : https://prove2.me/submissions/f7ef1a71-4e89-4ecd-a84c-295e6ba755e9

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_radial

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
theorem _root_.solution (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) (hz : z 0 ≠ 0)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖(y 0)⁻¹‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by
  have ht : 0 < ‖z 0‖ ^ 2 := by positivity
  have hφ' : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + (‖y 0‖ ^ 2)⁻¹) := by
    filter_upwards [hφ] with y hy
    rw [hy, norm_inv, inv_pow]
  have hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t⁻¹))
      (-(2 * (t * (1 + t)))⁻¹) t := by
    filter_upwards [lt_mem_nhds ht] with t ht
    have h0 : t ≠ 0 := ht.ne'
    have h1 : (1 + t⁻¹) ≠ 0 := by positivity
    have := (((hasDerivAt_inv h0).const_add 1).log h1).const_mul (1 / 2)
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  have hd2 : HasDerivAt (fun t : ℝ => -(2 * (t * (1 + t)))⁻¹)
      ((2 * ‖z 0‖ ^ 2 + 1) / (2 * (‖z 0‖ ^ 2) ^ 2 * (1 + ‖z 0‖ ^ 2) ^ 2)) (‖z 0‖ ^ 2) := by
    have h1 : (2 * (‖z 0‖ ^ 2 * (1 + ‖z 0‖ ^ 2))) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' (‖z 0‖ ^ 2)).mul
      ((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1)).const_mul 2).inv h1).neg
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  rw [maDens_radial φ _ _ (fun t => (2 * t + 1) / (2 * t ^ 2 * (1 + t) ^ 2)) z hφ' hd hd2, fsDens]
  have h1 : (1 + ‖z 0‖ ^ 2) ≠ 0 := by positivity
  have := Real.pi_pos
  field_simp
  ring
end ReciprocityTheory.AnForm
