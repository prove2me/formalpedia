-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_homForm_mem_eb6e66a4f8a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:26.123435+00:00
-- url     : https://prove2.me/submissions/e63eee92-13ea-4514-97a9-d58422b5e9e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_anchorMinor_eq_one_42e8acc3f4cd

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
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
namespace GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
theorem _root_.solution {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (q : Polynomial ℤ) (τ : Fin f)
    (I : PlIdx j m) (hq : Polynomial.aeval (rootCoord ζ ⟨τ, I⟩) q = 0) :
    homForm q τ I ∈ rootPointIdeal ζ := by
  show mConeMap (rootCoord ζ) (homForm q τ I) = 0
  have hA : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchorMinor_eq_one j m (ζ τ)
  simp only [homForm, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_C, hA, map_one, one_mul]
  rw [Polynomial.aeval_eq_sum_range] at hq
  calc _ = ∑ k ∈ Finset.range (q.natDegree + 1),
        C (q.coeff k • rootCoord ζ ⟨τ, I⟩ ^ k) * (X τ : MvPolynomial (Fin f) ℂ) ^ q.natDegree := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [← pow_mul_pow_sub (X τ : MvPolynomial (Fin f) ℂ) hk', zsmul_eq_mul, map_mul, map_pow,
          eq_intCast, map_intCast, mul_pow]
        ring
    _ = 0 := by rw [← Finset.sum_mul, ← map_sum, hq, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt
