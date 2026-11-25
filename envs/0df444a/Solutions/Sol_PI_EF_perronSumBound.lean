-- Prove2me | solution 1 for PI.EF.perronSumBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:44.462108+00:00
-- url     : https://prove2.me/submissions/c431bce0-82f3-442e-841f-83871b9d2f8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_pTerm_nonneg
import Theorems.Thm_PI_EF_sum_pTerm_le

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
theorem _root_.solution : PerronSumBound 500 := by
  intro u T hu hT
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  exact ⟨summable_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT),
    Real.tsum_le_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT)⟩
end PI.EF
