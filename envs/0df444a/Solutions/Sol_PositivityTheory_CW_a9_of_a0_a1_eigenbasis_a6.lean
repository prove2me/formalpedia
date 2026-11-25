-- Prove2me | solution 1 for PositivityTheory.CW.a9_of_a0_a1_eigenbasis_a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:36.892329+00:00
-- url     : https://prove2.me/submissions/deb5eed0-6f3c-408a-96e1-45fa28c3ea2c

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthPolynomialOperator
import Theorems.Thm_PositivityTheory_CW_NoncommutativeSwapSum_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A0 → A1 → CasimirIsRealScalar → A6 → A9 := by
  intro h0 h1 h3 h6 n ε V _ _ E hM
  obtain ⟨_, _, _, h0c⟩ := h0 n ε V E hM
  obtain ⟨_, _, hE1, _, hcomm, hL2, hZ2⟩ := h1 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3 n ε V E hM
  have hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w :=
    fun w => (h0c κ hκ w).2.2
  have hWU : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1)) ∈ U E 2 :=
    Submodule.sum_mem _ fun p _ => hcomm 1 2 _ (hE1 _ _) _ (hZ2 _ _)
  obtain ⟨C1, hC1, hW1⟩ := h6 n ε V E hM 2 _ hWU
  have hZZ : ∀ p : Fin n × Fin n,
      casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E ∈ U E 3 :=
    fun p => hcomm 2 2 _ hL2 _ (hZ2 _ _)
  choose Cp hCp0 hCp using fun p => h6 n ε V E hM 3 _ (hZZ p)
  have hCs : 0 ≤ ∑ p ∈ nc ε, Cp p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  refine ⟨C1 + ∑ p ∈ nc ε, Cp p ^ 2, by positivity, fun μ v hμ hv => ⟨?_, ?_⟩⟩
  · have hT : (∑ p ∈ nc ε, (E p.2 p.1 * Z ε E p.1 p.2 - Z ε E p.1 p.2 * E p.2 p.1))
        = (2 : ℂ) • ∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2 := by
      rw [Finset.sum_sub_distrib, NoncommutativeSwapSum.key ε E (κ : ℂ) hS, two_smul]
      abel
    have hWv := hW1 μ v hμ hv
    rw [Real.sq_sqrt (by linarith), hT, LinearMap.smul_apply, norm_smul] at hWv
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hWv
    have hTsum : ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)
        = -inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v) := by
      rw [LinearMap.sum_apply, inner_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hne : ε p.1 ≠ ε p.2 := (Finset.mem_filter.mp hp).2
      rw [hM.uni, adjSign, if_neg hne]
      simp
    have hv0 := norm_nonneg v
    have hTv0 := norm_nonneg ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)
    rw [hTsum, norm_neg]
    calc ‖inner ℂ v ((∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v)‖
        ≤ ‖v‖ * ‖(∑ p ∈ nc ε, E p.2 p.1 * Z ε E p.1 p.2) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (C1 * (1 + μ) * ‖v‖) := by
          apply mul_le_mul_of_nonneg_left _ hv0
          have : 0 ≤ C1 * (1 + μ) * ‖v‖ := by
            apply mul_nonneg (mul_nonneg hC1 (by linarith)) hv0
          linarith
      _ = C1 * (1 + μ) * ‖v‖ ^ 2 := by ring
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
  · have hs : Real.sqrt (1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
    have hp : ∀ p ∈ nc ε,
        ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          ≤ Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
      intro p _
      have h := hCp p μ v hμ hv
      have hm := mul_self_le_mul_self (norm_nonneg _) h
      calc ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
          = ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖
            * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ := sq _
        _ ≤ (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) * (Cp p * Real.sqrt (1 + μ) ^ 3 * ‖v‖) := hm
        _ = Cp p ^ 2 * (Real.sqrt (1 + μ) ^ 2) ^ 3 * ‖v‖ ^ 2 := by ring
        _ = Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by rw [hs]
    calc ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
        ≤ ∑ p ∈ nc ε, Cp p ^ 2 * (1 + μ) ^ 3 * ‖v‖ ^ 2 := Finset.sum_le_sum hp
      _ = (∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (C1 + ∑ p ∈ nc ε, Cp p ^ 2) * (1 + μ) ^ 3 * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          linarith
end PositivityTheory.CW
