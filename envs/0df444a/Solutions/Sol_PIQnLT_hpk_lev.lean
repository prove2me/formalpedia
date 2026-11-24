-- Prove2me | solution 1 for PIQnLT.hpk_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:27.030452+00:00
-- url     : https://prove2.me/submissions/05ad5717-37a0-4aa4-95bf-0afe10760afc

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_PIQnLT_lev_val

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
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution (p q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' p) (levPos k i r' q) = Hpk k r' p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, lev_val]
  have e1 : (↑p + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑p < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (↑q + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑q < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (i + r' ≤ p.val + i ∧ p.val + i ≤ i + r' + k ∧ p.val + i = q.val + i) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (↑p + i = i + r' + k) ↔ (↑p = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]
end PIQnLT
