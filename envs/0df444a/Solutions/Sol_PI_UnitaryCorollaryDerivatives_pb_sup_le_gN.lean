-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_sup_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:42.762543+00:00
-- url     : https://prove2.me/submissions/40ef5af2-fefe-435d-bbc8-f9c525f9d536

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_entry_le_gN

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
theorem _root_.solution (g : B.Mat k r) : ‖g‖ ≤ B.gN g := by
  have h0 : 0 ≤ B.gN g := by unfold B.gN; positivity
  exact (Matrix.norm_le_iff h0).2 (fun i j => pb_entry_le_gN g i j)
end PI.UnitaryCorollaryDerivatives
