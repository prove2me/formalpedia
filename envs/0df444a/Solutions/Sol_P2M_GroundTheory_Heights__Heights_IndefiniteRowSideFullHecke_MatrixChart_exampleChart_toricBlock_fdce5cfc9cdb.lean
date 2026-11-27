-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_MatrixChart_exampleChart_toricBlock_fdce5cfc9cdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:00:13.517424+00:00
-- url     : https://prove2.me/submissions/1e0aa4b2-b434-4eae-b6d9-edf35aa3dbd9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_IsOpenKappaOpenNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
theorem _root_.solution : ToricBlock exampleChart 1 where
  r_le := by norm_num
  B_support := by
    intro i j l h
    fin_cases j <;> fin_cases l <;> simp_all [exampleChart]
  sum_posDef := by
    have : ((∑ i, exampleChart.B i).submatrix (Fin.castLE (by norm_num : 1 ≤ 2))
        (Fin.castLE (by norm_num : 1 ≤ 2))) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      fin_cases i; fin_cases j
      simp [exampleChart]
    rw [this]
    exact PosDef.one
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
