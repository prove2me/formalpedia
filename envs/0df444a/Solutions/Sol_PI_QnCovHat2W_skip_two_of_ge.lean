-- Prove2me | solution 1 for PI.QnCovHat2W.skip_two_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:11:58.123359+00:00
-- url     : https://prove2.me/submissions/fce09b59-57c7-4ca2-9793-3fecadde7657

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : j ≤ Fin.castSucc j') :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 j j'.succ := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def, Fin.le_def] at *) <;> omega
end PI.QnCovHat2W
