-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_crossCount_le_of_heavy_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:13:47.952054+00:00
-- url     : https://prove2.me/submissions/e7756efd-52e1-41c6-a443-a60d2739e2c3

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_active_card_le_twice_degree_opposite_card
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_le_linear_of_card_ratio


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (spectral fraction uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hFractionBound : (exceptional.card : ℝ) ≤ fraction * S.card)
    (hMean : (Fintype.card A + Fintype.card B : Nat) * (exceptional.card : ℝ) ≤
      uniformBudget * Fintype.card G)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    (crossCount X.unionCayleyGraph exceptional
      (X.oppositeHeavySet side x cutoff (S \ exceptional)) : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt
        (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by
  apply crossCount_le_linear_of_card_ratio X.unionCayleyGraph
    (Fintype.card A + Fintype.card B) spectral fraction
    (2 * (Fintype.card A + Fintype.card B : Nat)) uniformBudget
    hSpectral hFraction (by positivity) hMixing exceptional S
    (X.oppositeHeavySet side x cutoff (S \ exceptional)) hFractionBound
  · exact_mod_cast X.active_card_le_twice_degree_opposite_card side x cutoff
      S exceptional hExceptional hCoverage
  · exact hMean
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
