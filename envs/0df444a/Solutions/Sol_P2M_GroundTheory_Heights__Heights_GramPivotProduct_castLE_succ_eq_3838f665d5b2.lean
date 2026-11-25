-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:22.967801+00:00
-- url     : https://prove2.me/submissions/daf61802-553d-4bc9-a38f-c1a872fb59e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct

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
open GroundTheory.Heights₂.Heights.GramPivotProduct
namespace GroundTheory.Heights₂.Heights.GramPivotProduct
theorem _root_.solution (d : ℕ) :
    (Fin.castLE (Nat.le_succ d) : Fin d → Fin (d + 1)) = Fin.castSucc := by
  funext i
  rfl
end GroundTheory.Heights₂.Heights.GramPivotProduct
