-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.evenState_exponential_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:16:56.967959+00:00
-- url     : https://prove2.me/submissions/f1237ada-c7fa-411b-b7c8-54e5037feb93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_pure_power_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    Real.exp ((k : ℝ) * Real.log 4) ≤
        (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤
        Real.exp ((k : ℝ) * Real.log (evenGrowthEnvelope S : ℝ)) := by
  have hs := S.three_le
  have hell : 0 < S.ell := by omega
  have hA : 0 < faceGrowthFactor S := by unfold faceGrowthFactor; positivity
  have hB : (0 : ℝ) < evenGrowthEnvelope S := by
    exact_mod_cast (show 0 < evenGrowthEnvelope S by unfold evenGrowthEnvelope; positivity)
  have hb := evenState_pure_power_bounds S k hk
  constructor
  · rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast hb.1
  · rw [Real.exp_nat_mul,Real.exp_log hB]
    exact_mod_cast hb.2
end QEC.Coding.BDL26QuantitativeBounds
