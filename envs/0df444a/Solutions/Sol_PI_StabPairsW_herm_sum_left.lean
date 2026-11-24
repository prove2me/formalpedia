-- Prove2me | solution 1 for PI.StabPairsW.herm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:31:27.922015+00:00
-- url     : https://prove2.me/submissions/b99b1b58-2d97-4aba-80d6-0187db6451e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

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
theorem _root_.solution (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ a, c a • v a) w = ∑ a, c a * herm (Hpk k r) (v a) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  simp [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
end PI.StabPairsW
