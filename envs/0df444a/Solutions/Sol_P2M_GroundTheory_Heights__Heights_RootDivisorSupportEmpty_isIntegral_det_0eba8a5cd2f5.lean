-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:12.691216+00:00
-- url     : https://prove2.me/submissions/d7ca5824-c053-447c-9dc1-32940f13e7e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDivSuppEmpty

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
open GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty
namespace GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  have : M.det ∈ integralClosure ℤ ℂ := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => h _ _) _
  exact this
end GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty
