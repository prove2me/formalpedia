-- Prove2me | solution 1 for PI.Dv.RK.mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:02.943202+00:00
-- url     : https://prove2.me/submissions/3c7a443b-ca92-49f6-ad81-58f2805e86c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.RK
theorem _root_.solution (T : GoodSet K G) (s : T.S) (z : MonoidAlgebra K G) :
    z * eS T s = ∑ g : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s g⁻¹ * (T.tau s).asAlgebraHom z)) •
        MonoidAlgebra.of K G g := by
  induction z using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, eS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
    rw [mul_smul_comm, ← map_mul (MonoidAlgebra.of K G), ← map_mul (T.tau s)]
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right]
  | add x y hx hy =>
    rw [add_mul, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_add, mul_add, map_add, mul_add, add_smul]
  | smul r x hx =>
    rw [smul_mul_assoc, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, mul_smul_comm, map_smul, smul_smul, smul_eq_mul]
    congr 1
    ring
end PI.Dv.RK
