-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.splitComplementLabel_splitLabel_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:19:20.509896+00:00
-- url     : https://prove2.me/submissions/650724fe-eef4-4cf4-be2c-64d706520c1b

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
theorem _root_.solution (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label q) :
    (S.splitComplementLabel T hST (S.splitLabel labels).2).2 = (T.splitLabel labels).2 := by
  funext i
  rfl
end QEC.Semantics.QuditSubsystem
