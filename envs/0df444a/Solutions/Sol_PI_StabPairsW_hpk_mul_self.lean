-- Prove2me | solution 1 for PI.StabPairsW.hpk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:03.704395+00:00
-- url     : https://prove2.me/submissions/10d27906-5282-470c-be0d-9fffb293abc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_apply
import Theorems.Thm_PI_StabPairsW_sgI_sgI
import Theorems.Thm_PI_StabPairsW_sgI_eq_iff

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
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [hpk_apply]
  rw [Finset.sum_eq_single (⟨sgI k r i.val, sgI_lt i⟩ : Fin (2 * r + k + 1))]
  · simp only [if_true, sgI_sgI]
    by_cases hil : i = l
    · subst hil
      by_cases hi : i.val = r + k
      · have h2 : sgI k r (r + k) = r + k := hi ▸ (sgI_eq_iff i).2 hi
        simp [hi, h2]
      · have h2 : ¬ sgI k r i.val = r + k := fun h => hi ((sgI_eq_iff i).1 h)
        simp [hi, h2]
    · have h3 : ¬ l.val = i.val := fun h => hil (Fin.ext h.symm)
      simp [h3, hil]
  · intro j _ hj
    have h4 : ¬ j.val = sgI k r i.val := fun h => hj (Fin.ext h)
    simp [h4]
  · simp
end PI.StabPairsW
