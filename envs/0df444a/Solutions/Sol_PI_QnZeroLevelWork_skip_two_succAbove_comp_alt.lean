-- Prove2me | solution 1 for PI.QnZeroLevelWork.skip_two_succAbove_comp_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:07.769114+00:00
-- url     : https://prove2.me/submissions/b0a6c9ba-2039-41de-ac29-497dc2b99348

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula
import Theorems.Thm_PI_QnZeroLevelWork_val_succAbove

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
theorem _root_.solution {t : ℕ} (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t) (hii : i.val ≤ i'.val) :
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j) := by
  have hv : (i.succAbove i').val = i'.val + 1 := by
    rw [val_succAbove]; split_ifs <;> omega
  apply Fin.ext
  rw [val_succAbove, val_succAbove]
  unfold skip2
  split_ifs <;> simp_all <;> omega
end PI.QnZeroLevelWork
