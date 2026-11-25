-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.eS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:01.787549+00:00
-- url     : https://prove2.me/submissions/c0498c1d-e9d8-48fd-a91f-a6f00543ac10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_phi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phi T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of z =>
    rw [Representation.asAlgebraHom_of, phi_apply, eS, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight z) _ _ ?_
    intro x
    simp only [Equiv.coe_mulRight, smul_mul_assoc, ← map_mul, mul_inv_rev]
    congr 2
    rw [mul_inv_cancel_left]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, map_add]
  | smul r a ha => rw [mul_smul_comm, ha, map_smul, map_smul]
end PI.Dv.HermitianFormEquivalence
