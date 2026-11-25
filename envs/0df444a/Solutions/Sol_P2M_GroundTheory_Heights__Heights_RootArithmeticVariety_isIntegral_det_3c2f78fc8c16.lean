-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:32.869445+00:00
-- url     : https://prove2.me/submissions/70d23181-87f2-4d53-a5ca-7ede36ffb68f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootArithVar

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
open GroundTheory.Heights₂.Heights.RootArithmeticVariety
namespace GroundTheory.Heights₂.Heights.RootArithmeticVariety
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun σ _ => ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => hM (σ i) i) _
end GroundTheory.Heights₂.Heights.RootArithmeticVariety
