-- Prove2me | solution 1 for P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:34.109569+00:00
-- url     : https://prove2.me/submissions/1725723f-4cdc-413b-9f22-6c6c1d71081d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc
import Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
import Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    ∑ a, c a • fvec k r z a = ∑ b : Fin r, c b.castSucc • bvec (eI k r b) + c (Fin.last r) • z := by
  rw [Fin.sum_univ_castSucc]
  simp only [fvec_castSucc', fvec_last']
end PI.PolynomialProperness.TauW
