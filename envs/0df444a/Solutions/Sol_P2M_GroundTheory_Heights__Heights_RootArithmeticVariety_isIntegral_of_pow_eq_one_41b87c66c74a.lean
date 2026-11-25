-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootArithmeticVariety_isIntegral_of_pow_eq_one_41b87c66c74a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:15.918274+00:00
-- url     : https://prove2.me/submissions/f1536cfb-756a-42cf-95d4-f708db1802b5

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
theorem _root_.solution {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by
    simp [Polynomial.eval₂_sub, h]⟩
end GroundTheory.Heights₂.Heights.RootArithmeticVariety
