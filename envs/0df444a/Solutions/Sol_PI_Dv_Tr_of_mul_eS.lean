-- Prove2me | solution 1 for PI.Dv.Tr.of_mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:24.017241+00:00
-- url     : https://prove2.me/submissions/d8cbc9d6-145e-43a6-909b-a0ff73f29b10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_phiS_apply

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) (y : G) :
    MonoidAlgebra.of K G y * eS T s = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.mul_sum]
  simp_rw [mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => ?_)
  have h : (y * x)⁻¹ * y = x⁻¹ := by group
  simp only [Equiv.coe_mulLeft, h, cf]
end PI.Dv.Tr
