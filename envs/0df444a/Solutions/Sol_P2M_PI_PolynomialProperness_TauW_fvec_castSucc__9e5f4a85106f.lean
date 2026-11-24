-- Prove2me | solution 1 for P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:55:10.617165+00:00
-- url     : https://prove2.me/submissions/d99ab362-71a9-437d-b16f-0fc43f48b049

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc

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
open PI PI.PolynomialProperness PI.PolynomialProperness.TauW
namespace PI.PolynomialProperness.TauW
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    fvec k r z b.castSucc = bvec (eI k r b) := by
  simp [fvec]
end PI.PolynomialProperness.TauW
