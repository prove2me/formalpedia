-- Prove2me | solution 1 for PI.Dv.Tr.eS_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:54.90817+00:00
-- url     : https://prove2.me/submissions/f47ea15c-4305-4d13-93af-6031f767dcc5

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
    eS T s * MonoidAlgebra.of K G y = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.sum_mul]
  simp_rw [smul_mul_assoc, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => ?_)
  have h : LinearMap.trace K (T.W s) (T.tau s ((x * y)⁻¹ * y)) =
      LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
    rw [show (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y by group, (T.tau s).map_mul, (T.tau s).map_mul,
      LinearMap.trace_mul_comm, ← mul_assoc, ← (T.tau s).map_mul, mul_inv_cancel, (T.tau s).map_one, one_mul]
  simp only [Equiv.coe_mulRight, h, cf]
end PI.Dv.Tr
