-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.mx_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:16.850878+00:00
-- url     : https://prove2.me/submissions/6c855d1a-a07b-42b8-a3e7-19430e5834d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_MxLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {k r : ℕ} {X : B.Mat k r} (h : B.unitLie k r X) : mx X ≤ 1 := by
  show ‖Matrix.of.symm X‖ ≤ 1
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  exact h.2 i j
end PI.UnitaryCorollaryDerivatives
