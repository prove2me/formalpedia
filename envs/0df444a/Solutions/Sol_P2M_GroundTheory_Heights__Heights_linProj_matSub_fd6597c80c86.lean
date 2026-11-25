-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:00.098673+00:00
-- url     : https://prove2.me/submissions/4c5e32e2-9a96-4384-bc7f-37c11cdcf648

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc

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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    linProj (matSub U π) v = linProj π (U v) := by
  simp only [linProj, matSub, unitary_apply_eq_sum, Matrix.vecMul, dotProduct]
  congr 1
  funext i
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm
end GroundTheory.Heights₂.Heights
