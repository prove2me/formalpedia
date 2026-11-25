-- Prove2me | solution 1 for PI.QmIndepW.quartic_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:47.130414+00:00
-- url     : https://prove2.me/submissions/030807ef-acee-4999-b734-59eb41c64fb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex
namespace PI.QmIndepW
theorem _root_.solution (a0 a1 a2 a3 a4 : ℂ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ 5 → a0 + a1 * t + a2 * (t : ℂ) ^ 2 + a3 * (t : ℂ) ^ 3 + a4 * (t : ℂ) ^ 4 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
  have h1 := h 1 le_rfl (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have h4 := h 4 (by norm_num) (by norm_num)
  have h5 := h 5 (by norm_num) le_rfl
  push_cast at h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination 5 * h1 - 10 * h2 + 10 * h3 - 5 * h4 + h5
  · linear_combination (-77/12 : ℂ) * h1 + (107/6 : ℂ) * h2 + (-39/2 : ℂ) * h3 + (61/6 : ℂ) * h4 + (-25/12 : ℂ) * h5
  · linear_combination (71/24 : ℂ) * h1 + (-59/6 : ℂ) * h2 + (49/4 : ℂ) * h3 + (-41/6 : ℂ) * h4 + (35/24 : ℂ) * h5
  · linear_combination (-7/12 : ℂ) * h1 + (13/6 : ℂ) * h2 + (-3 : ℂ) * h3 + (11/6 : ℂ) * h4 + (-5/12 : ℂ) * h5
  · linear_combination (1/24 : ℂ) * h1 + (-1/6 : ℂ) * h2 + (1/4 : ℂ) * h3 + (-1/6 : ℂ) * h4 + (1/24 : ℂ) * h5
end PI.QmIndepW
