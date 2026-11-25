-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:27:49.709143+00:00
-- url     : https://prove2.me/submissions/4ee64a57-3711-474b-8d0f-283aa94524b0

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GzEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by
  intro y
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hy : (n : ℝ) ≤ y := by
      have hk : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
      have hy0 : 0 ≤ y := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)] at hk
        exact lt_irrefl 0 hk
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)
    have hpos : (0 : ℝ) < n := by linarith
    have : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hpos, one_mul]
      exact hy
    rw [max_eq_left this]
  have hre : (Deduction.ramp (fun _ => 1) y).re
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_subset hsub]
    · simp [Deduction.ramp, Complex.re_sum]
    · intro n hn hn'
      have h0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hn'
        omega
      subst h0
      simp
  refine ⟨?_, ?_⟩
  · simp only [Formalism.Gz, Formalism.Sz, An.G]
    rw [hsum]
    ring
  · simp only [An.G, Deduction.G]
    rw [hre]
    ring
end UpperTheory.Comparison₂
