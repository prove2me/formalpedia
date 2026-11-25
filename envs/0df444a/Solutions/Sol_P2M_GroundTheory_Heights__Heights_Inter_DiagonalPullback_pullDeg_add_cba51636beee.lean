-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_add_cba51636beee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:11.475801+00:00
-- url     : https://prove2.me/submissions/5123b455-5fc7-42b1-9275-36116f7cc954

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e


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
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
theorem _root_.solution (j : Fin 2) (a b : T.YBlk → ℤ) :
    I1.pullDeg (diagonalBlockIndex j) (a + b) = I1.pullDeg (diagonalBlockIndex j) a + I1.pullDeg (diagonalBlockIndex j) b := by
  funext k
  by_cases h : ∃ k', diagonalBlockIndex j k' = k
  · obtain ⟨k', rfl⟩ := h
    simp only [Pi.add_apply, pullDeg_segreBlockEmbedding]
  · simp only [I1.pullDeg, Pi.add_apply, Function.extend_apply' _ _ _ h, Pi.zero_apply, add_zero]
end GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
