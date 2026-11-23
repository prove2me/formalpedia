-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_not_inW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:34.746489+00:00
-- url     : https://prove2.me/submissions/11625996-54b5-4870-82a9-ff1705169bed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply

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
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : ¬ inW k r i) : ¬ inW k r (piI k r i) := by
  unfold inW at hi ⊢
  unfold piI
  rw [if_neg hi]
  show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)
  have := i.isLt
  omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
