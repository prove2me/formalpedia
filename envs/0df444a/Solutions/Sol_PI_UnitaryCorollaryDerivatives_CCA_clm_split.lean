-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.clm_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:00.894857+00:00
-- url     : https://prove2.me/submissions/9c127b1c-c894-4204-b71a-6fc44719b74d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_reC_apply
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_imC_apply

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CCA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CCA
theorem _root_.solution (L : ℂ →L[ℝ] ℂ) (d : ℂ) : L d = L 1 * reC d + L Complex.I * imC d := by
  have h : d = (d.re : ℝ) • (1 : ℂ) + (d.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul, reC_apply, imC_apply, Complex.real_smul, Complex.real_smul]
  ring
end PI.UnitaryCorollaryDerivatives.CCA
