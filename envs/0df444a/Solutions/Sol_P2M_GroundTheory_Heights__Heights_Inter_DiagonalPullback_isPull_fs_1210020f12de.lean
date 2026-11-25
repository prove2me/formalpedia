-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_isPull_fs_1210020f12de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:25.103843+00:00
-- url     : https://prove2.me/submissions/b7417c97-796c-4230-9cb4-fb523f18862b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ofMetrics_fs_h_bd4ac42ff7dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
theorem _root_.solution (j : Fin 2) (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex j) (T.yyEmb (ι := ι) (ν := ν) (κ := κ) j)
      (HermLine.ofMetrics (fun k => fsMetric (T.yyIdx ι ν κ k)) c)
      (HermLine.ofMetrics (fun k => fsMetric (T.wwIdx ι ν κ k)) (I1.pullDeg (diagonalBlockIndex j) c)) := by
  refine ⟨rfl, fun z => ?_⟩
  rw [ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, pullDeg_eq_alt]
  fin_cases j
  · simp [T.pullDeg, T.yyEmb]
    rfl
  · simp [T.pullDeg, T.yyEmb]
    rfl
end GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
