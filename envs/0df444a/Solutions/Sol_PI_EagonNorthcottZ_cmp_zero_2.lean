-- Prove2me | solution 2 for PI.EagonNorthcottZ.cmp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:19.446215+00:00
-- url     : https://prove2.me/submissions/f75b7ccc-bbb8-4a67-bc12-94cc0e1fd21d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective

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
open MvPolynomial
namespace PI.EagonNorthcottZ
theorem _root_.solution {D : ℕ} (β : Fin D →₀ ℕ) : cmp β (0 : P D) = 0 := by simp [cmp]
end PI.EagonNorthcottZ
