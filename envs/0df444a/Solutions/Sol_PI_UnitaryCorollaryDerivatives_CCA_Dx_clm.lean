-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.Dx_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:49.344958+00:00
-- url     : https://prove2.me/submissions/ddee86a1-eb72-4f99-92a3-e49ce7622c1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_hasDx

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
theorem _root_.solution (x : Bool × Mat k r) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  funext g
  exact (hasDx x (L.differentiable.comp hf) g).unique (L.hasFDerivAt.comp_hasDerivAt _ (hasDx x hf g))
end PI.UnitaryCorollaryDerivatives.CCA
