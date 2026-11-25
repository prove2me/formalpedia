-- Prove2me | solution 1 for PI.QnHermHaar.skip1Eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:08:51.343283+00:00
-- url     : https://prove2.me/submissions/f601a53f-aae4-4d1d-a19c-8b03f1db14b1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Theorems.Thm_PI_QnHermHaar_valSuccAbove

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
theorem _root_.solution {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [valSuccAbove]
  unfold skip1
  split_ifs <;> simp
end PI.QnHermHaar
