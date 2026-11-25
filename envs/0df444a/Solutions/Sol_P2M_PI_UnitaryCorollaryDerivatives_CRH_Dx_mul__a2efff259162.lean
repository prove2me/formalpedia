-- Prove2me | solution 1 for P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:59.86873+00:00
-- url     : https://prove2.me/submissions/99f0016b-0cc9-4953-a526-dcd093335f3d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_hd_Dx

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
theorem _root_.solution (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hd_Dx x ha g).mul (hd_Dx x hb g)
  rw [h0] at h
  exact (hd_Dx x (ha.mul hb) g).unique h
end PI.UnitaryCorollaryDerivatives.CRH
