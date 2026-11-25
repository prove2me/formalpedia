-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.mul_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:32.64527+00:00
-- url     : https://prove2.me/submissions/094d6827-63c0-4af1-a60b-b84645772769

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshMean
theorem _root_.solution (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun ζ : ℂ => c * ζ) volume volume := by
  let f : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ c
  have hf : (fun ζ : ℂ => c * ζ) = ⇑f := rfl
  have hdet : LinearMap.det f = 1 := by
    have : LinearMap.det f = Algebra.norm ℝ c := (Algebra.norm_apply ℝ c).symm
    rw [this, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp
end ReciprocityTheory.AnForm.A.PshMean
