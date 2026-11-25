-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:15.675351+00:00
-- url     : https://prove2.me/submissions/39a33e22-17c4-46ae-b9f4-6ce422a90047

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e

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
    (π : Fin m → Fin n → ℂ) : matGauss (matSub U π) = matGauss π := by
  simp only [matGauss, matSub, sum_norm_sq_vecMul (unitMat_mem U)]
end GroundTheory.Heights₂.Heights
