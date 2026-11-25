-- Prove2me | solution 1 for PI.StabPairsW.hpk_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:09.571544+00:00
-- url     : https://prove2.me/submissions/41f10584-09a0-4dac-8015-8c20c9c4856e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_mul_self

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
theorem _root_.solution : (Hpk k r).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hpk_mul_self (k := k) (r := r))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1
end PI.StabPairsW
