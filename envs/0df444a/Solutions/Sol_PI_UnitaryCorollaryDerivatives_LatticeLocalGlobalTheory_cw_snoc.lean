-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.cw_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:12.378034+00:00
-- url     : https://prove2.me/submissions/a637366b-0d52-4bce-88be-42711924e28e

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
theorem _root_.solution (cost : B.Mat k r → ℕ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r) :
    cw cost (w ++ [x]) = cw cost w + cost x.2 := by
  simp [cw, List.map_append, List.sum_append]
end PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
