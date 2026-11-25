-- Prove2me | solution 1 for PI.Dv.Tr.mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:36.669032+00:00
-- url     : https://prove2.me/submissions/1dc63283-6803-4607-8268-2d94cc0061c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Theorems.Thm_PI_Dv_Tr_of_mul_eS

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
    a * eS T s = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [of_mul_eS, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, map_add]
  | smul r x hx => rw [smul_mul_assoc, hx, map_smul, map_smul]
end PI.Dv.Tr
