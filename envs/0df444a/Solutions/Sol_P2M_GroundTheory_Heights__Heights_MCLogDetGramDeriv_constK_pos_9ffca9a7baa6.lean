-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_constK_pos_9ffca9a7baa6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:12.14143+00:00
-- url     : https://prove2.me/submissions/b67bcdf5-0fb8-4ac4-9f8e-1b3bfaf1da21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCLogDetGramDeriv
namespace GroundTheory.Heights₂.Heights.MCLogDetGramDeriv
theorem _root_.solution (g k : ℕ) : 0 < constK g k := by
  unfold constK; positivity
end GroundTheory.Heights₂.Heights.MCLogDetGramDeriv
