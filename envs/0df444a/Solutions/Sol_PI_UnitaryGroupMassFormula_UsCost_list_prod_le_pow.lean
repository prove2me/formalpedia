-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.list_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:54.523553+00:00
-- url     : https://prove2.me/submissions/d7a02971-d697-47c1-ba36-56be14ebb60b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (l : List ℝ) (lam : ℝ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ lam) :
    l.prod ≤ lam ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hp : 0 ≤ l.prod := List.prod_nonneg (fun y hy => (h y (List.mem_cons_of_mem x hy)).1)
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hx.2 ih' hp (hx.1.trans hx.2)
end PI.UnitaryGroupMassFormula.UsCost
