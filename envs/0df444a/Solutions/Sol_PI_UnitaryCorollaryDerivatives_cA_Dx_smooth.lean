-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dx_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:10.268885+00:00
-- url     : https://prove2.me/submissions/e84eea77-6ee2-4fb2-bbdb-4224b15c4e99

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_eq

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
theorem _root_.solution (x : Bool × B.Mat k r) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dx x F) := by
  rw [cA_Dx_eq x (hF.differentiable (by simp))]
  exact (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply (dirL x).contDiff
end PI.UnitaryCorollaryDerivatives
