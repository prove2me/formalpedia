-- Prove2me | solution 1 for PI.lpLower_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:18.643232+00:00
-- url     : https://prove2.me/submissions/c1cdecdf-bfc8-4b36-942b-c365c5d52bb2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe
import Theorems.Thm_PI_lp_feasible_le
import Theorems.Thm_PI_lp_zero_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
open Finset
namespace PI
theorem _root_.solution : LpLower := by
  intro l d _ Ds hl hD
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hsup : sSup (lpFeasible l d Ds) ≤ (∑ s, Ds s) / ((l : ℝ) + 1) :=
    csSup_le ⟨0, lp_zero_mem l d Ds hD⟩ fun y hy => lp_feasible_le l d Ds hl hy
  have h1 : (l : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (l : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    exact this.ne'
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by ring
    rw [this]
    exact mul_ne_zero h2 h1
  have hid : (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - (∑ s, Ds s) / ((l : ℝ) + 1) =
      (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) := by
    have h4 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by ring
    rw [h4]
    field_simp
    ring
  unfold lpF
  linarith
end PI
