-- Prove2me | solution 1 for ReciprocityTheory.AnForm.maDens_fs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:18.287031+00:00
-- url     : https://prove2.me/submissions/b95653fe-b1eb-4ead-90ee-b0c8f4b2c1bb

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
theorem _root_.solution (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖y 0‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by
  have ht : 0 ≤ ‖z 0‖ ^ 2 := by positivity
  have hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t))
      ((2 * (1 + t))⁻¹) t := by
    filter_upwards [lt_mem_nhds (show (-1 : ℝ) < ‖z 0‖ ^ 2 by linarith)] with t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := (((hasDerivAt_id' t).const_add 1).log h1).const_mul (1 / 2)
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  have hd2 : HasDerivAt (fun t : ℝ => (2 * (1 + t))⁻¹) (-(2 * (1 + ‖z 0‖ ^ 2) ^ 2)⁻¹)
      (‖z 0‖ ^ 2) := by
    have h1 : (2 * (1 + ‖z 0‖ ^ 2)) ≠ 0 := by positivity
    have := (((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1).const_mul 2).inv h1
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  rw [maDens_radial φ _ _ (fun t => -(2 * (1 + t) ^ 2)⁻¹) z hφ hd hd2, fsDens]
  have h1 : (1 + ‖z 0‖ ^ 2) ≠ 0 := by positivity
  have := Real.pi_pos
  field_simp
  ring
end ReciprocityTheory.AnForm
