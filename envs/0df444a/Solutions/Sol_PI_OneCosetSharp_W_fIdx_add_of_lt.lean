-- Prove2me | solution 1 for PI.OneCosetSharp.W.fIdx_add_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:59.088886+00:00
-- url     : https://prove2.me/submissions/9aaf135f-8488-4e76-8671-5932e40219f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
namespace PI.OneCosetSharp.W
theorem _root_.solution (k₀ c n i : ℕ) (hi : i < c) : fIdx k₀ c n (k₀ + i) = n + i := by
  unfold fIdx
  rw [if_neg (by omega), if_pos (by omega)]
  omega
end PI.OneCosetSharp.W
