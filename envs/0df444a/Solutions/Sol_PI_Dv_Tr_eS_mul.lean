-- Prove2me | solution 1 for PI.Dv.Tr.eS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:17.847284+00:00
-- url     : https://prove2.me/submissions/a5a3e42d-3f00-4011-b771-fca02aaa38de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_eS_mul_of

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [eS_mul_of, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]
  | smul r x hx => rw [mul_smul_comm, hx, map_smul, map_smul]
end PI.Dv.Tr
