-- Prove2me | solution 1 for PI.EagonNorthcottZ.inx_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:03.642805+00:00
-- url     : https://prove2.me/submissions/a57472f8-1ad0-448f-bc2c-ecf01d5fa4bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
namespace PI.EagonNorthcottZ
theorem _root_.solution {D : ℕ} (i : Fin D) : inx (X i : S D) = xs i := by simp [inx, xs]
end PI.EagonNorthcottZ
