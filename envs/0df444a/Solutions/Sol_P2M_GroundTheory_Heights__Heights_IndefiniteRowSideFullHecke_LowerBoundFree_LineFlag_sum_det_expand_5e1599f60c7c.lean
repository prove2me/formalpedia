-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:27.684126+00:00
-- url     : https://prove2.me/submissions/133503ab-a266-4bc4-841e-5d75d7f929de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_fin_two_arrow_3d70d12f0270

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ q : Fin 2 → Fin 2, (∏ a, g (q a) a) * (detInt q : ℂ) = g.det := by
  rw [sum_fin_two_arrow, Matrix.det_fin_two]
  simp [detInt, Matrix.det_fin_two, Fin.prod_univ_two]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
