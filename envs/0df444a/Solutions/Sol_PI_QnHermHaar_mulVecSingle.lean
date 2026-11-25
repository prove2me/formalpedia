-- Prove2me | solution 1 for PI.QnHermHaar.mulVecSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:10.693814+00:00
-- url     : https://prove2.me/submissions/c3d1bb61-b6ca-404d-96d0-194084ef52c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (p p' : Fin m) :
    (Q *ᵥ Pi.single p (1 : ℂ)) p' = Q p' p := by
  first
    | (show ∑ j, Q p' j * (Pi.single p (1 : ℂ) : Fin m → ℂ) j = Q p' p
       simp [Pi.single_apply])
    | simp [Matrix.mulVec, Pi.single_apply]
end PI.QnHermHaar
