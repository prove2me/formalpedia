-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.cs_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:54.00181+00:00
-- url     : https://prove2.me/submissions/7a86badc-7c5d-4d4b-9092-1bb9f544b0cf

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
theorem _root_.solution (cost : Mat k r → ℕ) {w w' : List (Bool × Mat k r)} (h : w.Perm w') : cs cost w = cs cost w' := by
  unfold cs
  exact (h.map _).sum_eq
end PI.UnitaryCorollaryDerivatives.CRH
