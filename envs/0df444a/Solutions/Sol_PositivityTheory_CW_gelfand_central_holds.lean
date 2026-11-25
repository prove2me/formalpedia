-- Prove2me | solution 1 for PositivityTheory.CW.gelfand_central_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:36:10.462744+00:00
-- url     : https://prove2.me/submissions/d284d5cb-7d52-4903-8f69-a00ebb31098b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GelfandCentralHolds
import Theorems.Thm_PositivityTheory_CW_CasimirPowerCommute_comm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]
end PositivityTheory.CW
