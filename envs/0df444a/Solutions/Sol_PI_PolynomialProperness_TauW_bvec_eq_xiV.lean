-- Prove2me | solution 1 for PI.PolynomialProperness.TauW.bvec_eq_xiV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:40.397904+00:00
-- url     : https://prove2.me/submissions/add5ced2-7804-4159-a3f9-af2e3fe87335

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc
import Theorems.Thm_PI_PolynomialProperness_TauW_xiV_eq_sum

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
theorem _root_.solution (k r : ℕ) (b : Fin r) : bvec (eI k r b) = xiV k r (Pi.single b 1) := by
  rw [xiV_eq_sum]
  simp [Pi.single_apply, ite_smul]
end PI.PolynomialProperness.TauW
