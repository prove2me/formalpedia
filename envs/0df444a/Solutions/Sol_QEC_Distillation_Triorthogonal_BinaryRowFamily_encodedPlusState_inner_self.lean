-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:09:39.92268+00:00
-- url     : https://prove2.me/submissions/be8d70c3-f15c-45b1-8385-c7259f9d2ccb

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_inner_self

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
    inner Complex (R.encodedPlusState hR) (R.encodedPlusState hR) = 1 := by
  rw [encodedPlusState, (R.encoding hR).inner_map_map]
  exact logicalPlusState_inner_self OddRow
end QEC.Distillation.Triorthogonal.BinaryRowFamily
