-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:37.608835+00:00
-- url     : https://prove2.me/submissions/cac73454-366d-4caf-b226-9df5f7b29f46

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
theorem _root_.solution (z : (Σ k, ι k) → ℂ) (p a : Σ k, ι k) (hza : z a ≠ 0) (q : Polynomial ℤ) :
    eval z (map (Int.castRingHom ℂ) (homog q p a)) =
      z a ^ q.natDegree * q.eval₂ (Int.castRingHom ℂ) (z p / z a) := by
  rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum, homog, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
  simp only [map_mul, map_pow, map_intCast, map_X, eval_X, eq_intCast]
  conv_rhs => rw [← pow_mul_pow_sub (z a) hle, div_pow]
  field_simp
end GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
