-- Prove2me | solution 1 for PI.MSC.shapeColumnDegree_columnSizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:31.782357+00:00
-- url     : https://prove2.me/submissions/14230eb1-9f60-4500-b709-6a0f83cfc362

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
import Theorems.Thm_PI_MSC_card_colLen_gt

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
theorem _root_.solution (ν : YoungDiagram) : shapeDeg (sz0 ν) (n := ν.colLen 0) = nuR ν := by
  funext t
  exact card_colLen_gt ν t
end PI.MSC
