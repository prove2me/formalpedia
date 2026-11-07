-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVertices_card_bound_of_small_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:13:54.446865+00:00
-- url     : https://prove2.me/submissions/b5ffa81f-85b7-4ed0-a50c-ed1702675526

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVerticesOnSide_card_mul_le
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_card_group_mul_local_degree_eq_twice_card_square
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_ge_min_of_mem_dualTensorCode


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB Delta : Nat) (delta epsilon : ℝ)
    (hDelta : 0 < Delta) (hDeltaDistance : 0 < delta)
    (hCardA : Fintype.card A = Delta) (hCardB : Fintype.card B = Delta)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hDistanceA : delta * Delta ≤ (dA : ℝ)) (hDistanceB : delta * Delta ≤ (dB : ℝ))
    (side : Bool) (x : Word (ZMod 2) Square)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (hWeight : (HammingWeight x : ℝ) <
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))) :
    ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) := by
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hCount := X.activeVerticesOnSide_card_mul_le side x (min dA dB)
    (fun g hne => hammingWeight_ge_min_of_mem_dualTensorCode CA CB dA dB
      hA.choose_spec.2.2.2 hB.choose_spec.2.2.2 _ (hLocal g) hne)
  have hDistance : delta * Delta ≤ ((min dA dB : Nat) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min hDistanceA hDistanceB
  have hCount' : delta * Delta * (X.activeVerticesOnSide side x).card ≤
      2 * (HammingWeight x : ℝ) :=
    (mul_le_mul_of_nonneg_right hDistance (Nat.cast_nonneg _)).trans (by exact_mod_cast hCount)
  have hCard : (Fintype.card G : ℝ) * (Delta : ℝ) ^ 2 = 2 * Fintype.card Square := by
    have h := X.card_group_mul_local_degree_eq_twice_card_square
    rw [hCardA, hCardB] at h
    rw [← pow_two] at h
    exact_mod_cast h
  have hPower : (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) =
      (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
    calc
      _ = (Delta : ℝ) ^ ((1 : ℝ) + (1 / 2 + epsilon)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hD, Real.rpow_one]
  have hSmall := (lt_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) by positivity)).mp hWeight
  have hScaled := mul_le_mul_of_nonneg_right hCount'
    (show 0 ≤ 4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) by positivity)
  rw [hPower] at hSmall hScaled
  have hCardScaled := congrArg (fun z : ℝ => delta * z) hCard
  apply (le_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) by positivity)).mpr
  apply le_of_mul_le_mul_left (a := delta * (Delta : ℝ) ^ 2) ?_ (by positivity)
  nlinarith only [hSmall, hScaled, hCardScaled]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
