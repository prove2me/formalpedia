-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_norm_block_le_93e0782b40a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:15.372801+00:00
-- url     : https://prove2.me/submissions/25a21ea9-fdc2-43f0-b616-01af4120bdad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootLogNormBound

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
namespace GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
theorem _root_.solution (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    ‖WithLp.toLp 2 v‖ ≤ ‖a‖ * Real.sqrt ((1 + m : ℝ) ^ j) := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2
      = ‖a‖ ^ 2 * ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [hv, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h₃ j m Z hZ)) (norm_nonneg _)
end GroundTheory.Heights₂.Heights.RootLogNormBoundAlt
