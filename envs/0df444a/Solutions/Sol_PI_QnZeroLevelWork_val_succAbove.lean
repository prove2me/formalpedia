-- Prove2me | solution 1 for PI.QnZeroLevelWork.val_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:51.653988+00:00
-- url     : https://prove2.me/submissions/415c9b06-5ab7-49bc-8e66-33788e8ce153

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnZeroLevelWork
theorem _root_.solution {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  rcases Nat.lt_or_ge k.val p.val with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h), if_pos h]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h), if_neg (by omega)]
    simp
end PI.QnZeroLevelWork
