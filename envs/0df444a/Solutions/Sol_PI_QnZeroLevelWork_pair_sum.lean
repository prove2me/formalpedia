-- Prove2me | solution 1 for PI.QnZeroLevelWork.pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:11:38.703849+00:00
-- url     : https://prove2.me/submissions/53bad271-401c-4401-8501-fa28b965b386

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin (n + 2)) (G : Fin (n + 2) → M) :
    (∑ i' : Fin (n + 2), if i < i' then G i' else 0) =
      ∑ i'' : Fin (n + 1), if (i : ℕ) ≤ (i'' : ℕ) then G (i.succAbove i'') else 0 := by
  rw [Fin.sum_univ_succAbove _ i, if_neg (lt_irrefl i), zero_add]
  refine sum_congr rfl fun i'' _ => ?_
  have h : i < i.succAbove i'' ↔ (i : ℕ) ≤ (i'' : ℕ) := by
    rw [Fin.lt_def, val_succAbove]; split_ifs <;> omega
  simp only [h]
end PI.QnZeroLevelWork
