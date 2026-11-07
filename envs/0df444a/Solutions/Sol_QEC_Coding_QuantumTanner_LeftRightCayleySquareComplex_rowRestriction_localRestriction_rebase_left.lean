-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rowRestriction_localRestriction_rebase_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:26:32.525806+00:00
-- url     : https://prove2.me/submissions/d9430ae5-afa4-4adf-852c-e73ac913b9dd

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) :
    rowRestriction a (X.localRestriction (g, side) x) =
      rowRestriction (X.leftInverse a)
        (X.localRestriction (X.leftGenerator a * g, !side) x) := by
  ext b
  exact congrArg x (hX.1 g side a b)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
