-- Prove2me | solution 1 for PI.QnHermHaar.valSkip2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:48.364337+00:00
-- url     : https://prove2.me/submissions/beaa8bde-2e60-403f-8995-3a0f4d149b15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero

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
theorem _root_.solution {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) :
    (skip2 i i' j).val =
      if j.val < i.val then j.val else if j.val + 1 < i'.val then j.val + 1 else j.val + 2 := by
  unfold skip2
  split_ifs <;> rfl
end PI.QnHermHaar
