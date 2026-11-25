-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.cw_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:32.55959+00:00
-- url     : https://prove2.me/submissions/91cab42a-8a19-4c88-b722-80280599bf25

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
theorem _root_.solution (cost : B.Mat k r → ℕ) (u v : List (B.Mat k r)) :
    cw cost (wL u ++ wR v) = ((u ++ v).map cost).sum := by
  simp [cw, wL, wR, List.map_append, List.map_map, Function.comp_def]
end PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
