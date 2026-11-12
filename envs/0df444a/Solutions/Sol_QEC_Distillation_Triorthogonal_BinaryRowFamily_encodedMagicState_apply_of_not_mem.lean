-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_apply_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:09:36.353702+00:00
-- url     : https://prove2.me/submissions/16c938bf-ddd2-4618-b769-ad4e6beb045c

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem

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
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encodedMagicState hR : Qubit.QubitRegister Col) bits = 0 := by
  exact R.encoding_apply_of_not_mem hR (logicalMagicState OddRow) hbits
end QEC.Distillation.Triorthogonal.BinaryRowFamily
