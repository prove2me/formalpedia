-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.evenState_pure_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:13:12.126775+00:00
-- url     : https://prove2.me/submissions/bb7ae9d3-79ed-4cdc-8dc7-fdfaba4d9595

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeAsymptotics
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_upper
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    4 ^ k ≤ Fintype.card (state S (2*k)).presentation.Q ∧
      Fintype.card (state S (2*k)).presentation.Q ≤ evenGrowthEnvelope S ^ k := by
  have hlo := state_qubit_card_lower S (2*k)
  have hhi := state_qubit_card_upper S (2*k)
  have h8 : 8 ≤ (8 : Nat)^k := le_self_pow (by omega) (by omega)
  constructor
  · have he : (2 : Nat)^(2*k) = 4^k := by rw [pow_mul]; norm_num
    rw [he] at hlo
    omega
  · apply hhi.trans
    unfold evenGrowthEnvelope
    rw [mul_pow,pow_mul]
    exact Nat.mul_le_mul_right _ h8
end QEC.Coding.BDL26QuantitativeBounds
