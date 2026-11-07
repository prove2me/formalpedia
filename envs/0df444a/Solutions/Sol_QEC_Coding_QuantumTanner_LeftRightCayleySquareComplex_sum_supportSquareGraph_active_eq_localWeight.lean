-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_supportSquareGraph_active_eq_localWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:08:40.755875+00:00
-- url     : https://prove2.me/submissions/c335a8ef-f32b-4d9a-82cd-cc571ede806a

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_supportSquareGraph_eq_localWeight
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_supportSquareGraph_eq_zero_of_not_active

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g : G) :
    (∑ h ∈ X.activeVerticesOnSide side x, X.supportSquareGraph side x g h) =
      HammingWeight (X.localRestriction (g, side) x) := by
  rw [← X.sum_supportSquareGraph_eq_localWeight side x g]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro h _hh hnot
  exact X.supportSquareGraph_eq_zero_of_not_active side x g h hnot
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
