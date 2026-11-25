-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:24.514629+00:00
-- url     : https://prove2.me/submissions/01caf750-f35a-4467-9a3a-8fed6346bdd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2

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
theorem _root_.solution (hLL : LeadMinorLeading.Statement) {d : ℕ}
    (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {i : ℕ} (hi : i < d) :
    pivot (S.submatrix Fin.castSucc Fin.castSucc) i = pivot S i := by
  have h := hLL (d + 1) S d (Nat.le_succ d)
  rw [castLE_succ_eq] at h
  simp only [pivot, h (i + 1) (Nat.succ_le_of_lt hi), h i hi.le]
end GroundTheory.Heights₂.Heights.GramPivotProduct
