-- Prove2me | solution 1 for PI.EF.kb_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:26.809724+00:00
-- url     : https://prove2.me/submissions/f85a119e-a3b1-4be5-a298-1f4a756c4674

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
theorem _root_.solution {T : ℝ} (_hT : 0 < T) (y : ℝ) : kb T y ≤ 2 := by
  unfold kb
  split_ifs with h
  · exact le_rfl
  · have h' := not_le.mp h
    rw [div_le_iff₀ (by linarith)]
    linarith
end PI.EF
