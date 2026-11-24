-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:51.461165+00:00
-- url     : https://prove2.me/submissions/7e5ed547-cb55-4585-aa72-d624f0b312ec

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
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
