-- Prove2me | solution 1 for ReciprocityTheory.AnForm.integral_fsDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:07.753476+00:00
-- url     : https://prove2.me/submissions/abd430f5-29ed-468c-bd40-a942deae5d56

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Theorems.Thm_ReciprocityTheory_AnForm_integral_Ioi_fsDens_radial

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
theorem _root_.solution : ∫ z : ℂ, fsDens z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hf : ∀ p : ℝ × ℝ, p.1 • fsDens (Complex.polarCoord.symm p) =
      p.1 * (1 / (Real.pi * (1 + p.1 ^ 2) ^ 2)) * 1 := by
    intro p
    simp [fsDens, sq_abs]
  simp_rw [hf]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) (fun _ => (1 : ℝ)),
    integral_Ioi_fsDens_radial]
  have hπ := Real.pi_pos
  rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by linarith)]
  simp
  field_simp
  ring
end ReciprocityTheory.AnForm
