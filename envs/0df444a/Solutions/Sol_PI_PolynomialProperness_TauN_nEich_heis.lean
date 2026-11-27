-- Prove2me | solution 1 for PI.PolynomialProperness.TauN.nEich_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:06.875299+00:00
-- url     : https://prove2.me/submissions/5ce77cab-081a-4142-9730-5e7e80e10fcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermitianXiOrthogonal
import Theorems.Thm_PI_PolynomialProperness_TauN_nEich_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TauN
namespace PI.PolynomialProperness.TauN
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u - herm (Hpk k r) u (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z) • xiV k r ξ +
      herm (Hpk k r) u (xiV k r ξ) • (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z +
        ((1 : ℂ) / (2 * ((Tz k r z : ℝ) : ℂ))) • xiV k r ξ) := by
  rw [nEich_mulVec, Formalism.FourierDecayAlt.P.B2x4.herm_smul_right]
  have hc : star ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    simp [Complex.star_def]
  rw [hc]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring
end PI.PolynomialProperness.TauN
