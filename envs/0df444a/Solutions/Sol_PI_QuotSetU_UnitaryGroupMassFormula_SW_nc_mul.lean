-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.nc_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:34.018855+00:00
-- url     : https://prove2.me/submissions/98b26658-f836-464d-bf6f-446e8bd18d7b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup

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
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : NC k r a) (hb : NC k r b) : NC k r (a * b) := by
  intro i j hj hi
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hb j j hj (min_le_left _ _), if_pos rfl, mul_one]
    exact ha i j hj hi
  · intro l _ hlj
    by_cases hl : min j.val r ≤ l.val
    · rw [hb l j hj hl, if_neg hlj, mul_zero]
    · push_neg at hl
      have hlr : l.val < r := lt_of_lt_of_le hl (min_le_right _ _)
      have h := ha i l (by omega) (by rw [min_eq_left hlr.le]; omega)
      rw [h, if_neg (by intro h'; rw [h'] at hi; omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h
end PI.QuotSetU.UnitaryGroupMassFormula.SW
