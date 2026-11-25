-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_rootCoord_fd120b423998
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:07.657593+00:00
-- url     : https://prove2.me/submissions/a0cbfdc1-2f45-477a-a36d-6e2b4d43a9ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_det_3c2f78fc8c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_onePipe_e4cc74556326

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
theorem _root_.solution {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id]
  refine isIntegral_onePipe _ (fun a b => ?_) _ _
  obtain ⟨k, hk, h⟩ := hζ p.1 a b
  exact isIntegral_of_pow_eq_one hk h
end GroundTheory.Heights₂.Heights.RootArithmeticVariety
