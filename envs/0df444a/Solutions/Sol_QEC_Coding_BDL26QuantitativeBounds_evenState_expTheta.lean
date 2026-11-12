-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.evenState_expTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:36:05.654094+00:00
-- url     : https://prove2.me/submissions/e4ca4c79-50f9-45bb-bcc3-12b3bffc77bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_evenState_exponential_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : Nat, 1 ≤ k →
      Real.exp ((k : ℝ)*c) ≤ (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤ Real.exp ((k : ℝ)*C) := by
  have hs := S.three_le
  have hell : 0 < S.ell := by omega
  have hA : 0 < faceGrowthFactor S := by unfold faceGrowthFactor; positivity
  have hBnat : 1 < evenGrowthEnvelope S := by unfold evenGrowthEnvelope; nlinarith
  refine ⟨Real.log 4,Real.log (evenGrowthEnvelope S : ℝ),
    Real.log_pos (by norm_num),Real.log_pos (by exact_mod_cast hBnat),?_⟩
  exact fun k hk => evenState_exponential_bounds S k hk
end QEC.Coding.BDL26QuantitativeBounds
