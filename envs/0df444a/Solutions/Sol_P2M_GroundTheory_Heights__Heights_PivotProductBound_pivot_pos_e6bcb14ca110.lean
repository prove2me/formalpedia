-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:31.356834+00:00
-- url     : https://prove2.me/submissions/4d00570c-2cf9-46d2-81f3-82a0570c78d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotProductBound

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
open GroundTheory.Heights₂.Heights.PivotProductBound
namespace GroundTheory.Heights₂.Heights.PivotProductBound
theorem _root_.solution (hLB : LeadMinorBasic.Statement) {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i :=
  div_pos ((hLB d S).2.2 hS (i + 1) hi) ((hLB d S).2.2 hS i hi.le)
end GroundTheory.Heights₂.Heights.PivotProductBound
