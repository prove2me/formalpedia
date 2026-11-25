-- Prove2me | solution 1 for PI.EF.pTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:51.46251+00:00
-- url     : https://prove2.me/submissions/339ab802-faee-4290-bc92-8b651eb898c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound

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
theorem _root_.solution {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ pTerm u T n := by
  unfold pTerm
  have hk : 0 ≤ kb T (u / n) := by
    unfold kb
    split_ifs with h
    · norm_num
    · push_neg at h
      exact (one_div_pos.mpr (by linarith)).le
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)) hk
end PI.EF
