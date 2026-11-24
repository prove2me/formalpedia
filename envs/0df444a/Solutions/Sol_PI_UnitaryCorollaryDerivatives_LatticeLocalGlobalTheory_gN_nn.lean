-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.gN_nn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:05.807323+00:00
-- url     : https://prove2.me/submissions/2045f8e1-d041-469e-bb82-1caae9c5156a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
theorem _root_.solution (g : B.Mat k r) : 0 ≤ gN g := by
  first
  | (unfold gN; positivity)
  | (simp only [gN]; positivity)
  | (unfold B.gN; positivity)
end PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
