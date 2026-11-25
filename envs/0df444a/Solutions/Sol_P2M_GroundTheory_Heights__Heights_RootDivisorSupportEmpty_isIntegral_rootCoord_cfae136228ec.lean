-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:42.109707+00:00
-- url     : https://prove2.me/submissions/a1151721-6b69-46cd-a2a5-6681179da535

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDivSuppEmpty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_det_0eba8a5cd2f5

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
theorem _root_.solution {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  refine Fin.addCases (fun c => ?_) (fun c => ?_) ((p.2.1.orderEmbOfFin p.2.2) b)
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hz⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hz
end GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty
