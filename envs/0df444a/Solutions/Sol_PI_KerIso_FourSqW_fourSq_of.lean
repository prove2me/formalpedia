-- Prove2me | solution 1 for PI.KerIso.FourSqW.fourSq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:31.501994+00:00
-- url     : https://prove2.me/submissions/da01f9cb-440a-4d46-aced-07ee04ece4c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PI PI.KerIso PI.KerIso.FourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution (hA : OrthDiag) (hB : FromDiag) : FourSq := by
  intro K E _ _ _ _ _ cj n _ h2 hn hc hpos
  obtain ⟨b, q, hq, hb⟩ := hA K E cj n h2 hn hc hpos
  exact hB K E cj n b q hq hb
end PI.KerIso.FourSqW
