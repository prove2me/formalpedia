-- Prove2me | solution 1 for PI.Dv.TIW.eS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:44.250239+00:00
-- url     : https://prove2.me/submissions/7a860708-af5c-4670-96a8-68998eb10dff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_P2M_PI_Dv_TIW_theta_eq__d06abe871319

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
theorem _root_.solution (z : MonoidAlgebra K G) : eS T s * z = theta T s ((T.tau s).asAlgebraHom z) := by
  rw [theta_eq']
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, hx, hy, map_add]
    simp only [add_mul, map_add, mul_add, add_smul, Finset.sum_add_distrib]
  | single g r =>
    rw [Representation.asAlgebraHom_single, eS, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => ?_)
    simp only [Equiv.coe_mulRight, smul_mul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
      one_mul, smul_smul, smul_mul_assoc, mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    rw [← map_mul, mul_inv_rev, mul_inv_cancel_left, MonoidAlgebra.smul_single', MonoidAlgebra.smul_single', mul_one]
    congr 1
    ring
end PI.Dv.TIW
