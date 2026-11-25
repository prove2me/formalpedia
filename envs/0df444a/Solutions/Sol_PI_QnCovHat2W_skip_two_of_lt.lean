-- Prove2me | solution 1 for PI.QnCovHat2W.skip_two_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:43.806361+00:00
-- url     : https://prove2.me/submissions/6323b1ab-d7c4-4bda-96c6-d3128cf0ba1c

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
theorem _root_.solution {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : Fin.castSucc j' < j) :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 (Fin.castSucc j') j := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def] at *) <;> omega
end PI.QnCovHat2W
