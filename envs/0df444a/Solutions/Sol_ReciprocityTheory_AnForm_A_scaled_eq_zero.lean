-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.scaled_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:53.827108+00:00
-- url     : https://prove2.me/submissions/9daec307-59fb-4d3b-882d-a233a5347238

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ε ≤ ‖w‖) :
    ρ.scaled ε w = 0 := by
  have : ρ.toFun (ε⁻¹ • w) = 0 := by
    by_contra h
    have h1 := ρ.support_subset h
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h1
    have h2 : ε⁻¹ * ε ≤ ε⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (inv_pos.2 hε).le
    rw [inv_mul_cancel₀ hε.ne'] at h2
    linarith
  simp [Mollifier.scaled, this]
end ReciprocityTheory.AnForm.A
