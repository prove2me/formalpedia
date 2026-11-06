-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementBACLabel_splitLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:09:41.269277+00:00
-- url     : https://prove2.me/submissions/e98cdeae-2923-4a39-aee1-1fd4c1e75d2c

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
open QEC.Bounds.BPTEntropy.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
namespace QEC.Bounds.BPTEntropy.QuditSubsystem
theorem _root_.solution (S T : QuditSubsystem q)
    (hST : Disjoint S.selected T.selected) (labels : Qudit.Label q) :
    splitComplementBACLabel S T hST (T.splitLabel labels).2 =
      ((splitABCLabel S T labels).1, (splitABCLabel S T labels).2.2) := by
  apply Prod.ext <;> funext i <;> rfl
end QEC.Bounds.BPTEntropy.QuditSubsystem
