-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:59:16.439528+00:00
-- url     : https://prove2.me/submissions/ea50a943-b025-4317-8672-98348458ad3e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_Dw_const

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (c : ℂ) : PG 0 (fun _ : B.Mat k r => c) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun w _ _ g _ => ?_⟩⟩
  obtain ⟨c', hc', h⟩ := pb_Dw_const (k := k) (r := r) c w
  rw [h, Real.rpow_zero, mul_one]
  exact hc'
end PI.UnitaryCorollaryDerivatives
