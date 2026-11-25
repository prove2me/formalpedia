-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:28.843216+00:00
-- url     : https://prove2.me/submissions/c4d351ed-0d3a-432c-be4f-ed27f844240a

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
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : (1 : ℤ) ≤ |n| ^ 2 := one_le_pow₀ (Int.one_le_abs hn)
  rw [sq_abs] at h
  exact_mod_cast h
end GroundTheory.Heights₂.Heights.GramPivotProduct
