-- Prove2me | solution 1 for PI.EagonNorthcottZ.mu_inx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:09.499256+00:00
-- url     : https://prove2.me/submissions/883af9f4-5674-44bf-89b0-c740733cc497

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
theorem _root_.solution {D : ℕ} (s : S D) : mu (inx s) = s := by
  simp only [mu, inx]
  rw [aeval_rename, Sum.elim_comp_inl, aeval_X_left_apply]
end PI.EagonNorthcottZ
