-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.cw_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:05.667294+00:00
-- url     : https://prove2.me/submissions/e475245c-3a8c-403e-b834-9c3f2aae0afc

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
theorem _root_.solution (cost : B.Mat k r → ℕ) {w₁ w₂ w : List (Bool × B.Mat k r)} (hp : (w₁ ++ w₂).Perm w) :
    cw cost w₁ + cw cost w₂ = cw cost w := by
  unfold cw
  rw [← List.sum_append, ← List.map_append]
  exact (hp.map _).sum_eq
end PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
