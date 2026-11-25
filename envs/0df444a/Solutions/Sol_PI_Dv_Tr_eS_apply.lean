-- Prove2me | solution 1 for PI.Dv.Tr.eS_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:48.21333+00:00
-- url     : https://prove2.me/submissions/e040bfac-9e67-4e79-a9a8-4c69dd44a6ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) (x : G) :
    (eS T s).coeff x = cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
  classical
  rw [eS, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, cf]
  · intro y _ hy; simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hy]
  · simp
end PI.Dv.Tr
