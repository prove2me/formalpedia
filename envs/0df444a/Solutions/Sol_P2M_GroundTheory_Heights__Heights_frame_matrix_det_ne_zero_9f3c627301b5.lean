-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_frame_matrix_det_ne_zero_9f3c627301b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:24.423493+00:00
-- url     : https://prove2.me/submissions/13bb51a0-eb92-409c-9efa-c2b0a4a5a14f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open MvPolynomial
open scoped Matrix
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j
end GroundTheory.Heights₂.Heights
