-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.psum_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:05.128703+00:00
-- url     : https://prove2.me/submissions/020d1e9b-54e1-418a-bafe-770c54a6b08a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
variable {d : ℕ}
namespace PI.UnitaryGroupMassFormula.JCC.Ck
theorem _root_.solution (y h : Fin d → ℝ) (i : Fin d) :
    psum y h (i.val + 1) = psum y h i.val + h i • Pi.single i (1 : ℝ) := by
  funext l
  simp only [psum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hl : l = i
  · subst hl
    simp
  · have hne : l.val ≠ i.val := fun e => hl (Fin.ext e)
    rw [Pi.single_eq_of_ne hl, mul_zero, add_zero]
    by_cases hlt : l.val < i.val
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
end PI.UnitaryGroupMassFormula.JCC.Ck
