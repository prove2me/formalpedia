-- Prove2me | solution 1 for PI.PC.h_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:25.148356+00:00
-- url     : https://prove2.me/submissions/88d78069-664d-4db7-b2c6-c8b3ba1f816d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Theorems.Thm_PI_PC_h_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open scoped Nat
namespace PI.PC
theorem _root_.solution {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  by_cases ha' : 3 / 2 ≤ a
  · exact h_mono ha' hab
  push_neg at ha'
  have hb2 := h_mono (a := 2) (b := b) (by norm_num) hb
  have hla : log a ≤ a - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hq : (a - 1 / 2) * log a ≤ (a - 1 / 2) * (a - 1) :=
    mul_le_mul_of_nonneg_left hla (by linarith)
  have hq2 : (a - 1 / 2) * (a - 1) - a ≤ -1 := by nlinarith
  have h2 : -1 ≤ 2 * log 2 - 2 - log 2 / 2 := by
    have := Real.log_two_gt_d9
    linarith
  have e : (a - 1 / 2) * log a = a * log a - log a / 2 := by ring
  linarith
end PI.PC
