-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:30.201491+00:00
-- url     : https://prove2.me/submissions/df4d5b5e-c763-4774-8b70-46eb3f2841c7

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
theorem _root_.solution (hLB : LeadMinorBasic.Statement) {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i := by
  obtain ⟨-, -, h⟩ := hLB d S
  exact div_pos (h hS (i + 1) (Nat.succ_le_of_lt hi)) (h hS i hi.le)
end GroundTheory.Heights₂.Heights.GramPivotProduct
