-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dwl_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:22.38944+00:00
-- url     : https://prove2.me/submissions/619b7927-a164-4ada-af82-de23eaa17b72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_smooth

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dwl lam w F) := by
  induction w with
  | nil => exact hF
  | cons x w ih => exact (cA_Dx_smooth x ih).add (ih.const_smul (lam x))
end PI.UnitaryCorollaryDerivatives
