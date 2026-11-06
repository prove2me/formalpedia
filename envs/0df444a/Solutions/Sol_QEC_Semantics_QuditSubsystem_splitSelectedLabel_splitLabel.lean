-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.splitSelectedLabel_splitLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:19:19.833448+00:00
-- url     : https://prove2.me/submissions/7f46e032-4819-4f64-b41a-11307167f4a1

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label q) :
    S.splitSelectedLabel T hST (T.splitLabel labels).1 =
      ((S.splitLabel labels).1, (S.splitComplementLabel T hST (S.splitLabel labels).2).1) := by
  apply Prod.ext
  · funext i
    rfl
  · funext i
    rfl
end QEC.Semantics.QuditSubsystem
