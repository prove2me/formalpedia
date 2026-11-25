-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.n_sub_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:43:55.74761+00:00
-- url     : https://prove2.me/submissions/1fbfc41b-3248-4b17-a629-a72c2fc973b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_one_mem_UW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  exact ⟨1, one_mem_UW, n, hn, (Matrix.one_mul n).symm⟩
end PI.QuotSetU.UnitaryGroupMassFormula.SW
