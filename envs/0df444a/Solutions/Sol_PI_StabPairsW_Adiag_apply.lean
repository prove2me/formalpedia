-- Prove2me | solution 1 for PI.StabPairsW.Adiag_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:55.006824+00:00
-- url     : https://prove2.me/submissions/59019230-9378-4318-9c6e-9acae3ffb6f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_self_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    Adiag k r z a b = if a = Fin.last r ∧ b = Fin.last r then herm (Hpk k r) z z else 0 := by
  simp only [Adiag, Matrix.diagonal_apply, Tz, Complex.ofReal_neg, neg_neg, herm_self_re]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = Fin.last r <;> simp [ha]
  · rw [if_neg hab]
    have h2 : ¬ (a = Fin.last r ∧ b = Fin.last r) := fun h => hab (h.1.trans h.2.symm)
    rw [if_neg h2]
end PI.StabPairsW
