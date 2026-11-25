-- Prove2me | solution 1 for PI.Dv.TIW.mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:02.340847+00:00
-- url     : https://prove2.me/submissions/52e7303a-8187-42c0-93c4-295556be21ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_PI_Dv_TIW_theta_add
import Theorems.Thm_PI_Dv_TIW_theta_smul
import Theorems.Thm_PI_Dv_TIW_theta_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution (z : MonoidAlgebra K G) : z * eS T s = theta T s ((T.tau s).asAlgebraHom z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp [theta_zero]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, theta_add]
  | single g r =>
    rw [Representation.asAlgebraHom_single, theta_smul, eS, Finset.mul_sum, theta, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulLeft, mul_smul_comm, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      mul_one, smul_smul]
    rw [← map_mul, mul_inv_rev, inv_mul_cancel_right, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring
end PI.Dv.TIW
