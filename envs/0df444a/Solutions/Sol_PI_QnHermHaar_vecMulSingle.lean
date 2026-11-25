-- Prove2me | solution 1 for PI.QnHermHaar.vecMulSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:12.800452+00:00
-- url     : https://prove2.me/submissions/12c4c3f7-0cf5-4733-97a7-a0e6cfb846ad

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
theorem _root_.solution {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (l l' : Fin m) :
    (Pi.single l (1 : ℂ) ᵥ* P) l' = P l l' := by
  first
    | (show ∑ j, (Pi.single l (1 : ℂ) : Fin m → ℂ) j * P j l' = P l l'
       simp [Pi.single_apply])
    | simp [Matrix.vecMul, Pi.single_apply]
end PI.QnHermHaar
