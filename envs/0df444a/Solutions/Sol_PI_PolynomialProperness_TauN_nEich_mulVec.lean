-- Prove2me | solution 1 for PI.PolynomialProperness.TauN.nEich_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:21.49726+00:00
-- url     : https://prove2.me/submissions/59f530ff-70b1-440b-9b2f-d251eeb4d7d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermitianXiOrthogonal
import Theorems.Thm_PI_PolynomialProperness_TauN_vmv_mulVec
import Theorems.Thm_PI_PolynomialProperness_TauN_smul_mv
import Theorems.Thm_PI_PolynomialProperness_TauN_star_H_dot

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) •
      (-(herm (Hpk k r) u z • xiV k r ξ) + herm (Hpk k r) u (xiV k r ξ) • z +
        ((1 / 2 : ℂ) * herm (Hpk k r) u (xiV k r ξ)) • xiV k r ξ) := by
  simp only [nEich, Matrix.add_mulVec, Matrix.one_mulVec, smul_mv, Matrix.neg_mulVec, vmv_mulVec, star_H_dot,
    smul_smul]
end PI.PolynomialProperness.TauN
