-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.loglog_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:38.815693+00:00
-- url     : https://prove2.me/submissions/e6fbe194-4b9f-4bff-a55f-1f5f21f86f3a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (C a0 ε T : ℝ) (hε : 0 < ε) (ha0 : 0 ≤ a0) :
    ∃ Y : ℝ, ∀ y, Y ≤ y → 0 ≤ y → C * log (exp 1 + a0 + y) - ε * y < T := by
  have hc0 : 0 < |C| + 1 := by positivity
  have hK0 : 0 < 2 * (|C| + 1) / ε := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ε / 2 * (exp 1 + a0) + (|C| + 1) * (log (2 * (|C| + 1) / ε) - 1) :=
    ⟨_, rfl⟩
  refine ⟨2 * (A - T) / ε + 1, fun y hy hy0 => ?_⟩
  have he : (2 : ℝ) ≤ exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx : 0 < exp 1 + a0 + y := by linarith
  have hlog0 : 0 ≤ log (exp 1 + a0 + y) := Real.log_nonneg (by linarith)
  have h1 : log ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) ≤ (exp 1 + a0 + y) / (2 * (|C| + 1) / ε) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx.ne' hK0.ne'] at h1
  have h2 : C * log (exp 1 + a0 + y) ≤ (|C| + 1) * log (exp 1 + a0 + y) := by
    apply mul_le_mul_of_nonneg_right _ hlog0
    have := le_abs_self C
    linarith
  have h3 := mul_le_mul_of_nonneg_left
    (show log (exp 1 + a0 + y) ≤ (exp 1 + a0 + y) / (2 * (|C| + 1) / ε) + (log (2 * (|C| + 1) / ε) - 1) by linarith) hc0.le
  have h3' := mul_add (|C| + 1) ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) (log (2 * (|C| + 1) / ε) - 1)
  have h4 : (|C| + 1) * ((exp 1 + a0 + y) / (2 * (|C| + 1) / ε)) = ε / 2 * (exp 1 + a0 + y) := by
    field_simp
  have h5 : ε * (2 * (A - T) / ε + 1) = 2 * (A - T) + ε := by
    field_simp
  have h6 := mul_le_mul_of_nonneg_left hy hε.le
  nlinarith [h2, h3, h3', h4, h5, h6, hA]
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
