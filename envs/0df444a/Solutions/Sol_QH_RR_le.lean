-- Prove2me | solution 1 for QH.RR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:13.432977+00:00
-- url     : https://prove2.me/submissions/9b1025c4-1561-4c6e-af91-016d5b8141ca

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SumMinLeDiv
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_RRLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_KC_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_cN_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_min_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_vM_major
import Theorems.Thm_QH_exists_primePowerSum_le_mul_log


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ (N m₀ : ℕ) (w : ℝ), 1 ≤ w →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ w) → RR (cN y) m₀ N ≤ C * (Real.sqrt y + w * Real.log y) := by
  obtain ⟨C₁, hC₁, hsP⟩ := exists_primePowerSum_le_mul_log
  have hK := dA_KC_pos
  refine ⟨3 * dA_KC + C₁, by positivity, ?_⟩
  intro y hy N m₀ w hw hm
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hf0 : ∀ n, 0 ≤ cN y n := fun n => dA_cN_nonneg hy0 n
  have hsplit : RR (cN y) m₀ N ≤
      (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n) +
      ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n := by
    unfold RR
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := hf0 n
    by_cases h1 : IsPrimePow n <;> by_cases h2 : Even (n.factorization n.minFac) <;>
      by_cases h3 : n.minFac ∣ m₀ <;> simp [h1, h2, h3, this]
  have hA : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n)
      ≤ 3 * dA_KC * Real.sqrt y := by
    have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ Even (n.factorization n.minFac))
        ⊆ (Icc 1 N).image (fun m => m ^ 2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hev⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      rw [Nat.pow_minFac hk.ne', hp.minFac_eq, Nat.factorization_pow_self hp] at hev
      obtain ⟨j, rfl⟩ := hev
      refine Finset.mem_image.2 ⟨p ^ j, ?_, by ring⟩
      have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
      have h2 : p ^ j ≤ p ^ (j + j) := Nat.pow_le_pow_right hp.pos (by omega)
      exact Finset.mem_Icc.2 ⟨h1, h2.trans hnN⟩
    calc _ ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cN y n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
      _ = ∑ m ∈ Icc 1 N, cN y (m ^ 2) :=
          Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
      _ = ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m * min 1 (y / (m:ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, Nat.cast_pow]
      _ ≤ dA_KC * ∑ m ∈ Icc 1 N, min 1 (y / (m:ℝ) ^ 2) := by
          refine dA_vM_major _ (fun n => le_min zero_le_one (div_nonneg hy0 (by positivity))) ?_ N
          intro n hn
          apply min_le_min_left
          apply div_le_div_of_nonneg_left hy0 (pow_pos (Nat.cast_pos.mpr hn) 2)
          have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          push_cast
          nlinarith
      _ ≤ dA_KC * (3 * Real.sqrt y) :=
          mul_le_mul_of_nonneg_left (dA_sum_min_sq y (by linarith) N) hK.le
      _ = 3 * dA_KC * Real.sqrt y := by ring
  have hB : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n)
      ≤ C₁ * w * Real.log y := by
    set P := (Icc 1 N).filter (fun p => p.Prime ∧ p ∣ m₀ ∧ (p:ℝ) ≤ w) with hP
    have hmaps : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀),
        n.minFac ∈ P := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hd⟩ := hn
      have hpr : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
      have hle : n.minFac ≤ N := (Nat.minFac_le (by omega)).trans hnN
      simp only [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpr.one_lt.le, hle⟩, hpr, hd, hm _ hpr hd hle⟩
    have hcard : (P.card : ℝ) ≤ w := by
      have hs : P ⊆ Icc 1 ⌊w⌋₊ := by
        intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1, Nat.le_floor hp.2.2.2⟩
      have h1 := Finset.card_le_card hs
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
      calc (P.card : ℝ) ≤ ⌊w⌋₊ := by exact_mod_cast h1
        _ ≤ w := Nat.floor_le (by linarith)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ p ∈ P, C₁ * Real.log y := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine le_trans ?_ (hsP y hy N p)
          unfold sP
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
      _ = P.card * (C₁ * Real.log y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (C₁ * Real.log y) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₁.le hlog)
      _ = C₁ * w * Real.log y := by ring
  have hsq : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hwl : 0 ≤ w * Real.log y := mul_nonneg (by linarith) hlog
  calc RR (cN y) m₀ N ≤ _ := hsplit
    _ ≤ 3 * dA_KC * Real.sqrt y + C₁ * w * Real.log y := add_le_add hA hB
    _ ≤ (3 * dA_KC + C₁) * (Real.sqrt y + w * Real.log y) := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * dA_KC) hwl, mul_nonneg hC₁.le hsq]
end QH
