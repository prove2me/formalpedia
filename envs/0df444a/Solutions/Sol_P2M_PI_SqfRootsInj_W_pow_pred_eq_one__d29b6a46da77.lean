-- Prove2me | solution 1 for P2M_PI_SqfRootsInj_W_pow_pred_eq_one__d29b6a46da77
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:28.116942+00:00
-- url     : https://prove2.me/submissions/d2587271-978b-483e-a0fd-b556f293e2a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootsInj.W
theorem _root_.solution {K : Type*} [Field K] {x : K} (hx : x ≠ 0) {q : ℕ} (hq : 1 ≤ q)
    (h : x ^ q = x) : x ^ (q - 1) = 1 := by
  have h2 : x ^ (q - 1) * x = 1 * x := by rw [← pow_succ, Nat.sub_add_cancel hq, h, one_mul]
  exact mul_right_cancel₀ hx h2
end PI.SqfRootsInj.W
