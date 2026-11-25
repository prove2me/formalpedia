-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_detPoly_db93427849b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:37.174364+00:00
-- url     : https://prove2.me/submissions/3f9ad593-0b0a-4b70-82e2-a96de789e654

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Matrix MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) (x : Fin d × Fin n → ℂ) :
    eval x (detPoly M) = (Matrix.of (fun i k => x (i, k)) * M).det := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.mul_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
