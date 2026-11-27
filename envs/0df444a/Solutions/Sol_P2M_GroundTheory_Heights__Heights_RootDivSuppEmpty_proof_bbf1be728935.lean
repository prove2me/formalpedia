-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDivSuppEmpty_proof_bbf1be728935
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:12.890276+00:00
-- url     : https://prove2.me/submissions/db0d4036-009a-4131-9aca-382446e09d56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDivSuppEmpty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDivisorSupportEmpty_isIntegral_rootCoord_cfae136228ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e


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
open RootDivisorSupportEmpty
namespace GroundTheory.Heights₂.Heights
namespace RootDivSuppEmpty
theorem _root_.solution : RootDivSuppEmpty.Statement := by
  intro f j m ζ hζ
  ext Q
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hQmin, hrel⟩
  have hQp : Q.IsPrime := hQmin.1.1
  have hle := hQmin.1.2
  have hs : rootAnchorSection f j m ∈ Q := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨τ, -, hτ⟩ := (hQp.prod_mem_iff).1 hs
  obtain ⟨I, hI⟩ := hrel τ
  apply hI
  obtain ⟨p, hpm, hp⟩ := isIntegral_rootCoord hζ ⟨τ, I⟩
  set n := p.natDegree
  set G : MRing (plBlocks f j m) := ∑ k ∈ Finset.range (n + 1),
    C (p.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (n - k) with hGdef
  have hy0 : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor _ _ _
  have hG : G ∈ rootPointIdeal ζ := by
    rw [rootPointIdeal, mCoordIdeal, RingHom.mem_ker]
    simp only [hGdef, mConeMap, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      hy0, MvPolynomial.C_1, one_mul]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        algebraMap ℤ (MvPolynomial (Fin f) ℂ) (p.coeff k) * (C (rootCoord ζ ⟨τ, I⟩) * X τ) ^ k *
          (X τ : MvPolynomial (Fin f) ℂ) ^ (n - k) =
        C ((p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k) * X τ ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [eq_intCast, ← map_intCast (C : ℂ →+* MvPolynomial (Fin f) ℂ), mul_pow, C_mul, C_pow,
        ← Nat.add_sub_cancel' hkn, pow_add, Nat.add_sub_cancel_left]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
    have hsum : ∑ k ∈ Finset.range (n + 1), (p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k = 0 := by
      rw [← hp, Polynomial.eval₂_eq_sum_range]
      simp [n]
    rw [hsum, MvPolynomial.C_0, zero_mul]
  have hGQ : G ∈ Q := hle (Ideal.mem_sup_left hG)
  have h0 : Ideal.Quotient.mk Q (X ⟨τ, plAnchor j m⟩) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hτ
  have hpow : Ideal.Quotient.mk Q (X ⟨τ, I⟩) ^ n = 0 := by
    have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hGQ
    simp only [hGdef, map_sum, map_mul, map_pow, h0] at h1
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, pow_zero, mul_one,
      hpm.coeff_natDegree, map_one, map_one, one_mul] at h1
    · exact h1
    · intro k hk
      rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)), mul_zero]
  have := hQp
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_pow_eq_zero hpow)
end RootDivSuppEmpty
end GroundTheory.Heights₂.Heights
