-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:34.507127+00:00
-- url     : https://prove2.me/submissions/6735a427-08a5-4414-9a7b-3ed28a1760af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_isTwValueAt_intCast_8416e01d1382
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_basis_det_comp_6ef76de755bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_sum_det_expand_5e1599f60c7c

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
theorem _root_.solution (i0 : Fin 2) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz0 : z ⟨(), i0⟩ ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    IsPlueckerCoord DL.y (fun _ => i0) 0 (Pi.basisFun Ω (Fin 2)).det
      (Pi.basisFun Ω (Fin 2)) z (firstCols g 2 le_rfl) g.det := by
  refine ⟨fun q => (detInt q : ℂ), fun q => ?_, ?_⟩
  · rw [basis_det_comp]
    exact isTwValueAt_intCast _ _ (fun _ => hz0) _
  · rw [← sum_det_expand g]
    simp [firstCols]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
