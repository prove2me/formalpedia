-- Prove2me | solution 1 for P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:40.018595+00:00
-- url     : https://prove2.me/submissions/83efa19b-9540-4c62-a637-5bc728c7b56b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_Dw
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_add__06d740adb120

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
theorem _root_.solution (w : List (Bool × Mat k r)) {a b : Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = _
    rw [ih]
    exact Dx_add' x (dif (cd_Dw w ha)) (dif (cd_Dw w hb))
end PI.UnitaryCorollaryDerivatives.CRH
