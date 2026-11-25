-- Prove2me | solution 1 for PI.EF.kb_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:22.686482+00:00
-- url     : https://prove2.me/submissions/ccdd6424-1167-431c-b4de-33cbd165bc15

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
theorem _root_.solution {T d y : ℝ} (hT : 0 < T) (hd : 0 < d) (h : d ≤ |Real.log y|) :
    kb T y ≤ 2 / (T * d) := by
  have hTd : 0 < T * d := mul_pos hT hd
  have hle : T * d ≤ T * |Real.log y| := mul_le_mul_of_nonneg_left h hT.le
  unfold kb
  split_ifs with h1
  · rw [le_div_iff₀ hTd]
    linarith
  · calc 1 / (T * |Real.log y|) ≤ 1 / (T * d) := one_div_le_one_div_of_le hTd hle
      _ ≤ 2 / (T * d) := div_le_div_of_nonneg_right (by norm_num) hTd.le
end PI.EF
