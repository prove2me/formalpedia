-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:48.657726+00:00
-- url     : https://prove2.me/submissions/549f84af-4bcc-465b-b3a9-683282cb112c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m k : ℕ) (hk : q + m = k + r * a) :
    toN (r + a) (blockOut r a c κ q m) =
      C κ * ∑ nu ∈ partitionsOf r k, C (blockCoeff q m (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) := by
  rw [blockOut, map_sum, Finset.mul_sum]
  have hterm : ∀ lam ∈ partitionsOf r (q + m),
      toN (r + a) (blockCoeff q m lam • pushOut r a c κ lam) =
        if ∀ i, a ≤ lam i then C κ * (C (blockCoeff q m lam) *
          aeval (fun i : Fin (r + a) => C c.sign * X i)
            (schur (Fin (r + a)) (fun i => lam i - a))) else 0 := by
    intro lam _
    rw [map_smul, pushOut]
    split_ifs
    · rw [map_mul, toN_xSign, smul_eq_C_mul]
      simp only [toN, aeval_C, algebraMap_eq]
      ring
    · simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun nu i => a + nu i) (fun lam i => lam i - a) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [mem_partitionsOf_iff] at hnu
    rw [Finset.mem_filter, mem_partitionsOf_iff]
    refine ⟨⟨?_, fun i j hij => Nat.add_le_add_left (hnu.2 hij) a⟩, fun i => Nat.le_add_right a _⟩
    rw [Finset.sum_add_distrib, hnu.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · intro lam hlam
    rw [Finset.mem_filter, mem_partitionsOf_iff] at hlam
    rw [mem_partitionsOf_iff]
    refine ⟨?_, fun i j hij => Nat.sub_le_sub_right (hlam.1.2 hij) a⟩
    have h1 : ∑ i, (lam i - a) + ∑ i : Fin r, a = ∑ i, lam i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlam.2 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  · intro nu _
    funext i
    simp
  · intro lam hlam
    rw [Finset.mem_filter] at hlam
    funext i
    exact Nat.add_sub_cancel' (hlam.2 i)
  · intro nu _
    simp
end GroundTheory.Heights₂.Heights.RestTerms.Top
