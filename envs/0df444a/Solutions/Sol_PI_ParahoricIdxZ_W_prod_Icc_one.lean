-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.prod_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:40.142314+00:00
-- url     : https://prove2.me/submissions/81dd72ac-9e04-432c-a9bd-9f14b3ab9c00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution (g : ℕ → ℝ) (n : ℕ) : ∏ i ∈ Icc 1 n, g i = ∏ j ∈ range n, g (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]
end PI.ParahoricIdxZ.W
