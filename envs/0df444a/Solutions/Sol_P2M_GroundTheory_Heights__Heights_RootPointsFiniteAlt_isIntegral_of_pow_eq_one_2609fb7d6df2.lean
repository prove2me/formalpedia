-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_isIntegral_of_pow_eq_one_2609fb7d6df2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:14:11.470147+00:00
-- url     : https://prove2.me/submissions/ba5c357e-bd7f-46ff-ba60-d84397608b7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite

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
open GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
variable {K : Type*} {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
theorem _root_.solution {x : ℂ} {k : ℕ} (hk : 0 < k) (hx : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hx]⟩
end GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
