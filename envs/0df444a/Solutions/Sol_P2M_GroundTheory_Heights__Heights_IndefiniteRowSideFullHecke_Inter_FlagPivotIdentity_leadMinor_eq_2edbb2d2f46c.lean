-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotIdentity_leadMinor_eq_2edbb2d2f46c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:12.44142+00:00
-- url     : https://prove2.me/submissions/6abb1fc8-9172-4aad-a9c1-004869fd36bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotIdentity

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
variable {R : Type} [CommRing R] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
theorem _root_.solution (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotIdentity
