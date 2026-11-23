-- Prove2me | solution 1 for PI.EF.kb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:19.504799+00:00
-- url     : https://prove2.me/submissions/ab48ee68-1fa2-4252-a214-c461f69bef20

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
theorem _root_.solution {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ kb T y := by
  unfold kb
  split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))
end PI.EF
