-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:49.47695+00:00
-- url     : https://prove2.me/submissions/d80a3fe7-10dd-4631-a0c8-1697df671069

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_card_bound_of_density_gap

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (Delta : Nat) (hDelta : 0 < Delta) (delta : ℝ) (hDeltaDistance : 0 < delta)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (4 * Real.sqrt Delta))
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card +
        (delta * Delta / 2) * Fintype.card G ≤ (cutoff : ℝ) * Fintype.card G) :
    (X.oppositeHeavySet side x cutoff normal).card ≤
      64 / (delta ^ 2 * Delta) * (X.activeVerticesOnSide side x).card := by
  have hd : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hGap : 0 < delta * Delta / 2 := by positivity
  have h := X.oppositeHeavySet_card_bound_of_density_gap hX side x cutoff normal
    (4 * Real.sqrt Delta) (delta * Delta / 2) (by positivity) hGap hMixing hDensity
  have hRoot : (Real.sqrt (Delta : ℝ)) ^ 2 = Delta := Real.sq_sqrt hd.le
  have hScaled : (Delta : ℝ) *
      (delta ^ 2 * Delta * (X.oppositeHeavySet side x cutoff normal).card) ≤
      (Delta : ℝ) * (64 * (X.activeVerticesOnSide side x).card) := by
    nlinarith
  have hCancel := le_of_mul_le_mul_left hScaled hd
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hDeltaDistance) hd)).mpr
  nlinarith
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
