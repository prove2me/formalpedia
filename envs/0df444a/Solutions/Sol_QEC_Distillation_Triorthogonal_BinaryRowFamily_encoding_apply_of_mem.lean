-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.encoding_apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:08:19.172296+00:00
-- url     : https://prove2.me/submissions/8e375a0d-e389-4d8a-b74c-3ee889dbe4b0

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (psi : Qubit.QubitRegister OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encoding hR psi : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar *
        psi ((R.logicalBasisEquivLogicalQuotient hR).symm
          (Submodule.Quotient.mk
            ⟨bitstringWordEquiv Col bits, hbits⟩)) := by
  change R.cssNormalizationScalar *
      PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister
        R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) bits = _
  rw [PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) hbits]
  rfl
end QEC.Distillation.Triorthogonal.BinaryRowFamily
