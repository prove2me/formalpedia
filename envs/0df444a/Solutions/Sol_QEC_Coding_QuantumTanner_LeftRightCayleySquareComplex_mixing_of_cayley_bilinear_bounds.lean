-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.mixing_of_cayley_bilinear_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:24:38.557329+00:00
-- url     : https://prove2.me/submissions/6feab2cb-702d-497a-b440-ce3cf8e5c7c7

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_leftCayleyGraph_regular
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rightCayleyGraph_regular
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_leftCayleyGraph_symmetric
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rightCayleyGraph_symmetric
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_eq_compose
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_regular
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_symmetric
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_regular
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_symmetric
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_add
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_compose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_toExpanderMixingBound
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
    (lambda mu : ℝ) (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hLeft : HasMeanZeroBilinearBound X.leftCayleyGraph lambda)
    (hRight : HasMeanZeroBilinearBound X.rightCayleyGraph mu) :
    (∀ side, HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) (lambda * mu)) ∧
    HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (lambda + mu) := by
  constructor
  · intro side
    apply HasMeanZeroBilinearBound.toExpanderMixingBound
      (X.squareGraph_symmetric side) (X.squareGraph_regular side) (mul_nonneg hLambda hMu)
    rw [X.squareGraph_eq_compose hX]
    exact HasMeanZeroBilinearBound.compose (Fintype.card A) (Fintype.card B)
      X.leftCayleyGraph_symmetric X.leftCayleyGraph_regular
      X.rightCayleyGraph_symmetric X.rightCayleyGraph_regular hLambda hMu hLeft hRight
  · apply HasMeanZeroBilinearBound.toExpanderMixingBound
      X.unionCayleyGraph_symmetric X.unionCayleyGraph_regular (add_nonneg hLambda hMu)
    exact hLeft.add hRight
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
