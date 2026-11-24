-- Prove2me | solution 1 for PI.StabPairsW.hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:43.613693+00:00
-- url     : https://prove2.me/submissions/cdf61d0e-872c-42a8-8414-c6053016119b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_apply

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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) j = (if j.val = r + k then -1 else 1) * v ⟨sgI k r j.val, sgI_lt j⟩ := by
  rw [Matrix.mulVec, dotProduct]
  simp_rw [hpk_apply]
  rw [Finset.sum_eq_single (⟨sgI k r j.val, sgI_lt j⟩ : Fin (2 * r + k + 1))]
  · simp
  · intro l _ hl
    have h4 : ¬ l.val = sgI k r j.val := fun h => hl (Fin.ext h)
    simp [h4]
  · simp
end PI.StabPairsW
