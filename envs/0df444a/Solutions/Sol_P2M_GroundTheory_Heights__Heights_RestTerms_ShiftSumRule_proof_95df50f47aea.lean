-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_proof_95df50f47aea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:06.285294+00:00
-- url     : https://prove2.me/submissions/9db6e160-e28b-4bfa-a866-93ebd6d2baff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2

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
open MvPolynomial Finset
noncomputable section
open ShiftSumRule
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace ShiftSumRule
theorem _root_.solution (hS : ShiftTotalValues.Statement)
    (h1 : FlagIntegralKillsPowerSums.Statement) : ShiftSumRule.Statement := by
  classical
  intro r a hr ha Q hQ
  have h0 : flagIntegralLinear 1 (r + a)
      (∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last)) = 0 :=
    (hS 1 r a 0).1.1
  have hnat : ∀ (n : ℕ) (G : RootRing 1 (r + a)),
      flagIntegralLinear 1 (r + a) ((n : RootRing 1 (r + a)) * G) =
        n * flagIntegralLinear 1 (r + a) G := by
    intro n G
    rw [show (n : RootRing 1 (r + a)) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul,
      smul_eq_mul]
  have hexp : ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        pderiv ((0 : Fin 1), i) (restPolynomial 1 r a .last) =
      ∑ k ∈ Icc 1 (r + a),
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) := by
    rw [hQ]
    simp only [Fin.sum_univ_one]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← sum_first_pow, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_mul, pderiv_blockPowerSum]; ring
  rw [hexp, map_sum] at h0
  have hval : ∀ k ∈ Icc 1 (r + a),
      flagIntegralLinear 1 (r + a)
        (blockPowerSum 1 (r + a) k 0 *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
              pderiv ((0 : Fin 1), i) (Q k 0) +
          (k : RootRing 1 (r + a)) *
            (blockPowerSum 1 (r + a) (k - 1) 0 - smallPowerSum 1 r a .last (k - 1) 0) *
              Q k 0) =
        (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [map_add, show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) k 0 * _) = 0 from
      h1 1 (r + a) k 0 _ hk.1 hk.2, zero_add, mul_assoc, hnat, sub_mul, map_sub]
  rw [Finset.sum_congr rfl hval] at h0
  have hI : Icc 1 (r + a) = insert 1 (Icc 2 (r + a)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp)] at h0
  have hk1 : ((1 : ℕ) : ℚ) *
      (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (1 - 1) 0 * Q 1 0) -
        flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (1 - 1) 0 * Q 1 0)) =
      (a : ℚ) * flagIntegral 1 (r + a) (Q 1 0) := by
    have e1 : blockPowerSum 1 (r + a) 0 0 = ((r + a : ℕ) : RootRing 1 (r + a)) := by
      simp [blockPowerSum]
    have e2 : smallPowerSum 1 r a .last 0 0 = ((r : ℕ) : RootRing 1 (r + a)) := by
      simp [smallPowerSum]
    rw [Nat.sub_self, e1, e2, hnat, hnat]
    change ((1 : ℕ) : ℚ) * (((r + a : ℕ) : ℚ) * flagIntegral 1 (r + a) (Q 1 0) -
      (r : ℚ) * flagIntegral 1 (r + a) (Q 1 0)) = _
    push_cast; ring
  have hk2 : ∀ k ∈ Icc 2 (r + a),
      (k : ℚ) * (flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) -
          flagIntegralLinear 1 (r + a) (smallPowerSum 1 r a .last (k - 1) 0 * Q k 0)) =
        -restTerm 1 (r + a) Q k 0 (smallPowerSum 1 r a .last (k - 1) 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [show flagIntegralLinear 1 (r + a) (blockPowerSum 1 (r + a) (k - 1) 0 * Q k 0) = 0 from
      h1 1 (r + a) (k - 1) 0 _ (by omega) (by omega), zero_sub, restTerm, mul_neg]
    rfl
  rw [hk1, Finset.sum_congr rfl hk2, Finset.sum_neg_distrib] at h0
  linarith
end ShiftSumRule
end GroundTheory.Heights₂.Heights.RestTerms
