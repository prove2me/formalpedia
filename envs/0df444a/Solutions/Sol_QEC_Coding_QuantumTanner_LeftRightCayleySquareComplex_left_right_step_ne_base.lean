-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.left_right_step_ne_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:52:19.623226+00:00
-- url     : https://prove2.me/submissions/e1a08d6c-f67f-40c4-878e-3845ed8744c9

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (a : A) (b : B) :
    X.leftGenerator a * g * X.rightGenerator b ≠ g := by
  intro h
  apply X.noConjugacy g a (X.rightInverse b)
  rw [X.rightGenerator_inverse]
  exact (eq_mul_inv_iff_mul_eq).2 h
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
