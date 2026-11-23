-- Prove2me | solution 1 for PI.EF.nearB_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:53.617104+00:00
-- url     : https://prove2.me/submissions/d95883e4-59a4-4d8a-9a34-11b8c3732fe5

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
theorem _root_.solution {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ nearB u T n := by
  unfold nearB
  have h4 : 0 ≤ 4 * u / T := by positivity
  split_ifs with h1 h2
  · apply div_nonneg h4
    have h5 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    linarith
  · norm_num
  · apply div_nonneg h4
    have h5 : (⌊u⌋₊ : ℝ) + 1 < n := by exact_mod_cast (by omega : ⌊u⌋₊ + 1 < n)
    linarith
end PI.EF
