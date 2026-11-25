-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.Dx_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:45.731133+00:00
-- url     : https://prove2.me/submissions/0502871a-1ace-4757-a430-dc7e3d4c2fb4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_hasDx
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_sm_diff
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_clm_split

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
theorem _root_.solution (x : Bool × Mat k r) {χ : ℂ → ℂ} {ψ : Mat k r → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) :
    Dx x (fun g => χ (ψ g)) = fun g => (fun z => fderiv ℝ χ z 1) (ψ g) * reC (Dx x ψ g)
      + (fun z => fderiv ℝ χ z Complex.I) (ψ g) * imC (Dx x ψ g) := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hχd : Differentiable ℝ χ := by
    first
    | exact hχ.differentiable (by simp)
    | exact hχ.differentiable le_top
    | exact hχ.differentiable (by norm_num)
  have h1 := hasDx x (sm_diff hψ) g
  have h2 : HasFDerivAt χ (fderiv ℝ χ (ψ g)) (ψ (crv x g 0)) := by
    rw [h0]; exact (hχd (ψ g)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := hasDx x (sm_diff (hχ.comp hψ)) g
  have h5 : Dx x (fun g => χ (ψ g)) g = fderiv ℝ χ (ψ g) (Dx x ψ g) := h4.unique h3
  rw [h5, clm_split]
end PI.UnitaryCorollaryDerivatives.CCA
