-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QnFFZero.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:10.696283+00:00
-- url     : https://prove2.me/submissions/d3ea0644-1cf6-4b8f-a51e-79f6398d676e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelGeneralLinear_GlevZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QnFFZero_ell_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QnFFZero
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.QnFFZero
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) : psi k r z c 1 = 1 := by
  simp [psi, ell_one k r z hz]
end PI.UnitaryGroupMassFormula.QnFFZero
