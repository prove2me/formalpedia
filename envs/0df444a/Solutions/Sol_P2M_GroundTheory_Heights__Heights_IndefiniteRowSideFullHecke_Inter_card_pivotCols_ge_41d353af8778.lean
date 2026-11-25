-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotCols_ge_41d353af8778
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:07.976058+00:00
-- url     : https://prove2.me/submissions/26373e83-198d-4872-81d7-8419cbf5fbf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg

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
theorem _root_.solution {n : ℕ} (a : Fin (n - 1)) :
    Fintype.card {b : Fin n // (a : ℕ) ≤ b} = n - a := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin n => (a : ℕ) ≤ b) = Finset.Ici (Fin.castLE (Nat.sub_le n 1) a) := by
    ext b; simp [Fin.le_def]
  rw [this, Fin.card_Ici]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
