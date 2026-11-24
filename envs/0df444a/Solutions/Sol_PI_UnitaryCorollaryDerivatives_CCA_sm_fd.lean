-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.sm_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:49:42.725559+00:00
-- url     : https://prove2.me/submissions/959de8c7-f9e5-44c8-a9d0-2d54469a9b4c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA

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
theorem _root_.solution {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) := by
  first
  | exact (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const
end PI.UnitaryCorollaryDerivatives.CCA
