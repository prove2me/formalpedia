-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.cd_Dx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:18.948848+00:00
-- url     : https://prove2.me/submissions/648be577-0bc5-4184-b306-3df8bbcf9d70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_Dx_fd

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
theorem _root_.solution (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (dif hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff
end PI.UnitaryCorollaryDerivatives.CRH
