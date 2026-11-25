-- Prove2me | solution 1 for PI.MSC.rowLen_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:22.729901+00:00
-- url     : https://prove2.me/submissions/8b4b68c6-8c18-4903-acde-d8b174d7fd53

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC
namespace PI.MSC
theorem _root_.solution (ν : YoungDiagram) {t : ℕ} (ht : ν.colLen 0 ≤ t) : ν.rowLen t = 0 := by
  by_contra h
  have h0 : (t, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero h)
  have h1 := YoungDiagram.mem_iff_lt_colLen.1 h0
  omega
end PI.MSC
