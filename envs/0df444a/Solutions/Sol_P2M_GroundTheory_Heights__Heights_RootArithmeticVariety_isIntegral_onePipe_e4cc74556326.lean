-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:18.396488+00:00
-- url     : https://prove2.me/submissions/a8441782-ada4-4917-9b93-6196c51a620a

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
theorem _root_.solution {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by
  simp only [onePipe, Matrix.of_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) b
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    exact hZ a i
end GroundTheory.Heights₂.Heights.RootArithmeticVariety
