-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_zero_37c4884a24bb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:34.665871+00:00
-- url     : https://prove2.me/submissions/a38ef528-1dcc-4bc1-b747-e4c34db72f3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagPivot

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
