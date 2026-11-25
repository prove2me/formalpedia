-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_qf_star_mul_self_975fe84e53ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:32.257318+00:00
-- url     : https://prove2.me/submissions/a692dd30-9a84-4b03-8cea-4498a2187474

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (B : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    qf (star B * B) v = ∑ i, (B *ᵥ v) i ^ 2 := by
  unfold qf
  rw [← Matrix.mulVec_mulVec, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    Matrix.dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, sq]
end GroundTheory.Heights₂.Heights.KTheta
