-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:21:50.301053+00:00
-- url     : https://prove2.me/submissions/20a44633-aeef-4816-9fc0-f87942c918cc

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem

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
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedPlusState hR : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar * logicalUniformScalar OddRow := by
  rw [encodedPlusState, R.encoding_apply_of_mem hR _ hbits]
  rfl
end QEC.Distillation.Triorthogonal.BinaryRowFamily
