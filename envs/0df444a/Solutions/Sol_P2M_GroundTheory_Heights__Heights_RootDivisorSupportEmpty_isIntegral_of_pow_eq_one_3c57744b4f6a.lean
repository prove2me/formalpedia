-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_of_pow_eq_one_3c57744b4f6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:14.000347+00:00
-- url     : https://prove2.me/submissions/a8f704c7-8551-498b-ba9f-587dc26e0fea

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
theorem _root_.solution {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hz]⟩
end GroundTheory.Heights₂.Heights.RootDivisorSupportEmpty
