-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:46.793971+00:00
-- url     : https://prove2.me/submissions/9fc41bb3-65d2-4996-a6f9-f2b0985cea87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace OtherFactorBound
theorem _root_.solution (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
  set e := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hs : c.sign = 1 ∨ c.sign = -1 := by cases c <;> simp [SmallBlock.sign]
  have hex : ∀ nu : Fin r → ℕ, ∃ T : MvPolynomial (Fin (r + a)) ℚ, nu ∈ partitionsOf r k →
      powerSumHom (r + a) T = aeval (fun i : Fin (r + a) => C c.sign * X i)
          (schur (Fin (r + a)) nu) ∧
        coeff e T = c.sign ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0 := by
    intro nu
    by_cases hnu : nu ∈ partitionsOf r k
    · have hmem := hnu
      simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hmem
      obtain ⟨T, hT1, hT2⟩ := hS (r + a) r k hk1 hkN nu c.sign hs
        (fun i j hij => hmem.2 i j hij) hmem.1
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hnu⟩
  choose T hT using hex
  have hSsum : S = ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * T nu := by
    apply Flag.powerSumHom_injective
    rw [hSeq, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, (hT nu hnu).1]
    congr 1
    simp [powerSumHom]
  have hterm : ∀ nu ∈ partitionsOf r k,
      |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * coeff e (T nu)| =
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) else 0) / k := by
    intro nu hnu
    rw [(hT nu hnu).2, abs_mul, abs_mul, abs_pow]
    have habs : |c.sign| = 1 := by rcases hs with h | h <;> simp [h]
    rw [habs, one_pow, one_mul, Nat.abs_cast]
    split_ifs
    · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]; ring
    · simp
  calc |coeff e S|
      = |∑ nu ∈ partitionsOf r k,
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * coeff e (T nu)| := by
        rw [hSsum, coeff_sum]
        simp only [coeff_C_mul]
    _ ≤ ∑ nu ∈ partitionsOf r k,
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * coeff e (T nu)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)|) / k := by
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_filter]
        simp only [Nat.abs_cast]
    _ ≤ (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
        gcongr
        exact hH r a k (fun nu => ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)) hk1
          (fun nu _ => by simp)
end OtherFactorBound
end GroundTheory.Heights₂.Heights.RestTerms
