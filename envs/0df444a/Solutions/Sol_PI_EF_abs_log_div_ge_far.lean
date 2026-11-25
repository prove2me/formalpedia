-- Prove2me | solution 1 for PI.EF.abs_log_div_ge_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:57.882344+00:00
-- url     : https://prove2.me/submissions/7576ac14-48f1-4c04-a8f0-9965399ae220

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (h : x ≤ u / 2 ∨ 2 * u ≤ x) :
    Real.log 2 ≤ |Real.log (u / x)| := by
  rcases h with h | h
  · have h2 : 2 ≤ u / x := by
      rw [le_div_iff₀ hx]
      linarith
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)
  · have h2 : 2 ≤ x / u := by
      rw [le_div_iff₀ hu]
      linarith
    have hflip : Real.log (u / x) = -Real.log (x / u) := by
      rw [← Real.log_inv, inv_div]
    rw [hflip, abs_neg]
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)
end PI.EF
