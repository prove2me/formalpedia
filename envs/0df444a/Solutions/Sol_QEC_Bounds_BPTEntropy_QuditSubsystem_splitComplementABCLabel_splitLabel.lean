-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.QuditSubsystem.splitComplementABCLabel_splitLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:09:36.726163+00:00
-- url     : https://prove2.me/submissions/f8975719-a437-4520-a201-d6bb203b6682

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
    splitComplementABCLabel S T hST (S.splitLabel labels).2 =
      (splitABCLabel S T labels).2 := by
  apply Prod.ext <;> funext i <;> rfl
end QEC.Bounds.BPTEntropy.QuditSubsystem
