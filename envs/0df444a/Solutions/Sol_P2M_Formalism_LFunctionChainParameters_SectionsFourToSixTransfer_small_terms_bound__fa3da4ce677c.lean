-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_small_terms_bound__fa3da4ce677c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:35.142946+00:00
-- url     : https://prove2.me/submissions/708c5a37-e5b2-4b7c-9fb2-d9e0a066fab4

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_text_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : SmallText := by
  intro ε e cT c6 hε he hc6
  obtain ⟨x₀, h⟩ := text_key ε (e + 2) hε
  refine ⟨max x₀ (2 * |cT| / c6 + 1), fun x k nT hx hn0 hn hk hnk => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 2 * |cT| / c6 + 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx8, _, _, ha, hbp, hK⟩ := h x hx0
  have hxp : 0 < x := by linarith
  have hKp : 0 < x ^ (e + 2) := Real.rpow_pos_of_pos hxp _
  obtain ⟨_, k2, _⟩ := hK _ hKp le_rfl
  have hXp : 0 < XpTx x ε := Real.exp_pos _
  have hKX : x ^ (e + 2) ≤ XpTx x ε := by
    unfold bpTx at k2
    rw [← mul_div_assoc, div_le_iff₀ hXp] at k2
    have : x ^ (e + 2) * aTx x ε ≤ XpTx x ε * aTx x ε := by linarith
    exact le_of_mul_le_mul_right this ha
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hxp _
  have eK : x ^ (e + 2) = x ^ e * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have q1 : nT * (x / k) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hk hxp]; nlinarith
  have q2 : nT * (x / XpTx x ε) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hXp hxp]
    have : nT * x * x ≤ x ^ e * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn (sq_nonneg x)
      nlinarith
    linarith
  have q0 : 0 ≤ nT * (x / k + x / XpTx x ε) :=
    mul_nonneg hn0 (add_nonneg (div_nonneg hxp.le hk.le) (div_nonneg hxp.le hXp.le))
  have q3 : nT * (x / k + x / XpTx x ε) ≤ 2 / x := by
    have : 2 / x = 1 / x + 1 / x := by ring
    rw [this, mul_add]; linarith
  have h1 : cT * nT * (x / k + x / XpTx x ε) ≤ |cT| * (2 / x) := by
    calc cT * nT * (x / k + x / XpTx x ε) = cT * (nT * (x / k + x / XpTx x ε)) := by ring
      _ ≤ |cT| * (nT * (x / k + x / XpTx x ε)) := mul_le_mul_of_nonneg_right (le_abs_self _) q0
      _ ≤ |cT| * (2 / x) := mul_le_mul_of_nonneg_left q3 (abs_nonneg _)
  have h2 : |cT| * (2 / x) < c6 := by
    rw [← mul_div_assoc, div_lt_iff₀ hxp]
    have : 2 * |cT| / c6 < x := by linarith
    rw [div_lt_iff₀ hc6] at this
    linarith
  linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
