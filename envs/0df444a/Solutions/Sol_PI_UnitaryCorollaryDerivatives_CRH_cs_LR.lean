-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.cs_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:40.304029+00:00
-- url     : https://prove2.me/submissions/9f872417-0604-499b-9d2c-bbbd29a88e8a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CRH
theorem _root_.solution (cost : Mat k r → ℕ) (u v : List (Mat k r)) :
    ((u ++ v).map cost).sum = cs cost (wL u ++ wR v) := by
  simp [cs, wL, wR, List.map_append, List.map_map, Function.comp_def]
end PI.UnitaryCorollaryDerivatives.CRH
