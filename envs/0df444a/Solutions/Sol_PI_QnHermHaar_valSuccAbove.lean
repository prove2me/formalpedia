-- Prove2me | solution 1 for PI.QnHermHaar.valSuccAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:24.54508+00:00
-- url     : https://prove2.me/submissions/cb1794cf-edd5-4808-b5e3-1a03e4d67159

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
theorem _root_.solution {n : ℕ} (p : Fin (n + 1)) (x : Fin n) :
    (p.succAbove x).val = if x.val < p.val then x.val else x.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
end PI.QnHermHaar
