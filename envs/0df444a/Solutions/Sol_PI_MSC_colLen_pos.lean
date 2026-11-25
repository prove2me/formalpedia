-- Prove2me | solution 1 for PI.MSC.colLen_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:47.525145+00:00
-- url     : https://prove2.me/submissions/62fd3ece-8e10-49d5-ac4e-56b21f570e68

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
theorem _root_.solution (ν : YoungDiagram) (c : Fin (ν.rowLen 0)) : 0 < ν.colLen c := by
  exact YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 c.2)
end PI.MSC
