-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.Dx_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:14.431797+00:00
-- url     : https://prove2.me/submissions/4bf47ebf-d389-4f38-93ed-704515ae7014

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_hd_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dirL_apply


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
theorem _root_.solution (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  have h := (hf (crv x g 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  rw [crv_zero] at h
  rw [dirL_apply]
  exact (hd_Dx x hf g).unique h
end PI.UnitaryCorollaryDerivatives.CRH
