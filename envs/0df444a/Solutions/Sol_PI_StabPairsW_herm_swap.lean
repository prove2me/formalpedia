-- Prove2me | solution 1 for PI.StabPairsW.herm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:33.097393+00:00
-- url     : https://prove2.me/submissions/9fb19f3f-a54f-4844-a75a-c8099839036f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_conjTranspose

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
theorem _root_.solution (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.dotProduct_mulVec, Matrix.star_dotProduct, Matrix.star_mulVec, star_star,
    hpk_conjTranspose]
end PI.StabPairsW
