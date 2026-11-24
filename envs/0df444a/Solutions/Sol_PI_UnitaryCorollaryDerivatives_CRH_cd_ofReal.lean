-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.cd_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:49:44.466417+00:00
-- url     : https://prove2.me/submissions/8ebb7e75-9563-44fc-b079-fc0e0e229758

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
theorem _root_.solution {ψ : Mat k r → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (fun g => ((ψ g : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hψ
end PI.UnitaryCorollaryDerivatives.CRH
