-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnRestriction_localRestriction_rebase_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:26:43.788799+00:00
-- url     : https://prove2.me/submissions/d2bc3d52-be76-45d5-a65f-b3106d2f3299

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
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    columnRestriction b (X.localRestriction (g, side) x) =
      columnRestriction (X.rightInverse b)
        (X.localRestriction (g * X.rightGenerator b, !side) x) := by
  ext a
  exact congrArg x (hX.2 g side a b)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
