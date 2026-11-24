-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:23.021997+00:00
-- url     : https://prove2.me/submissions/5fff7439-b8f5-4314-a056-6399675fbd01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul

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
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  have hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
end HermNorm
end GroundTheory.Heights₂.Heights
