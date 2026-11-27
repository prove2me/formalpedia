-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexJacobian_proof_878d7125df17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:03.183709+00:00
-- url     : https://prove2.me/submissions/c39a7ba0-68c3-4a75-affd-fae5082cfde8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_add_a05a839368cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_one_75e32c5c0dc9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ComplexJacobian
theorem _root_.solution : ComplexJacobian.Statement := by
  intro p q M
  have hR : 1 + (realForm M)ᵀ * realForm M = realForm (1 + Mᴴ * M) := by
    rw [realForm_add, realForm_one, realForm_mul, realForm_conjTranspose]
  set z := (1 + Mᴴ * M).det with hz
  have hstar : star z = z := by
    rw [hz, ← Matrix.det_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : z.im = 0 := by
    have := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [hR, det_realForm, Complex.normSq_apply, him]
  apply Complex.ext <;> simp [sq, him, ← hz]
end ComplexJacobian
end GroundTheory.Heights₂.Heights
