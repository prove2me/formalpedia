-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:08.799923+00:00
-- url     : https://prove2.me/submissions/59a6ca51-93f4-4b0c-b2cd-5fb6ae8899ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_EfRankSumMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_sum_ef
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finite_pts
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finrank_as
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_free_as


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
namespace PI.UnitaryGroupMassFormula.EfRankSum
theorem _root_.solution : PI.EfRankSum := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _
  haveI : Module.Free O ↥(As O A) := free_as O K A
  exact ⟨finite_pts O A, by rw [sum_ef O A hϖ, finrank_as O K A]⟩
end PI.UnitaryGroupMassFormula.EfRankSum
