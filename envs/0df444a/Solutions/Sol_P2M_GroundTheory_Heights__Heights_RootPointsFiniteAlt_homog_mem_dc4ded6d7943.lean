-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:41.29009+00:00
-- url     : https://prove2.me/submissions/08fff017-7b96-4d98-aa92-f1625dadc1b6

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
theorem _root_.solution (y : (Σ k, ι k) → ℂ) (k : K) (i i₀ : ι k) (ha : y ⟨k, i₀⟩ = 1) (q : Polynomial ℤ)
    (hq : q.eval₂ (Int.castRingHom ℂ) (y ⟨k, i⟩) = 0) :
    homog q ⟨k, i⟩ ⟨k, i₀⟩ ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  have hterm : ∀ n ∈ Finset.range (q.natDegree + 1),
      mConeMap y (C (q.coeff n) * X ⟨k, i⟩ ^ n * X ⟨k, i₀⟩ ^ (q.natDegree - n)) =
        MvPolynomial.C ((q.coeff n : ℂ) * y ⟨k, i⟩ ^ n) * MvPolynomial.X k ^ q.natDegree := by
    intro n hn
    have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
    simp only [mConeMap, map_mul, map_pow, map_intCast, aeval_X, ha, map_one, one_mul]
    conv_rhs => rw [← pow_mul_pow_sub (MvPolynomial.X k) hle]
    rw [aeval_C, eq_intCast (algebraMap ℤ (MvPolynomial K ℂ))]
    ring
  rw [homog, map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  have : ∑ n ∈ Finset.range (q.natDegree + 1), (q.coeff n : ℂ) * y ⟨k, i⟩ ^ n = 0 := by
    rw [← hq, Polynomial.eval₂_eq_sum_range]; rfl
  rw [this, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.RootPointsFiniteAlt
