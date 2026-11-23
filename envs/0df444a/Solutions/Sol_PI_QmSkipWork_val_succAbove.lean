-- Prove2me | solution 1 for PI.QmSkipWork.val_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:19.243654+00:00
-- url     : https://prove2.me/submissions/0114321c-e8f8-42ea-8cd3-69f44f9c41d9

import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkipSuccessorIndex_SkipSucc2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSkipWork
namespace PI.QmSkipWork
theorem _root_.solution {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt p k (by simpa [Fin.lt_def] using h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc p k (by simp [Fin.le_def]; omega)]
    simp
end PI.QmSkipWork
