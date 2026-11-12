-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:09:48.669317+00:00
-- url     : https://prove2.me/submissions/533421aa-59c9-44f5-bda7-5b9d6c5f9f44

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_inner_self

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
attribute [-instance] Fintype.ofFinite
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    inner Complex (R.encodedMagicState hR) (R.encodedMagicState hR) = 1 := by
  rw [encodedMagicState, (R.encoding hR).inner_map_map]
  exact logicalMagicState_inner_self OddRow
end QEC.Distillation.Triorthogonal.BinaryRowFamily
