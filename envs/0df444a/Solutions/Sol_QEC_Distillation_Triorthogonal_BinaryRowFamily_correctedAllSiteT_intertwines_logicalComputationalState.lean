-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_intertwines_logicalComputationalState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:41:25.852519+00:00
-- url     : https://prove2.me/submissions/d96b6710-4cd0-41c3-9c89-d2ee75229a72

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_allSiteT_logicalComputationalState
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_encodedComputationalState

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) :
    R.correctedAllSiteT
        (R.encoding hR (logicalComputationalState label) : Qubit.QubitRegister Col) =
      (R.encoding hR
        ((allSiteT (Index := OddRow)) (logicalComputationalState label)) :
          Qubit.QubitRegister Col) := by
  change R.correctedAllSiteT
      (R.encodedComputationalState hR label : Qubit.QubitRegister Col) = _
  rw [R.correctedAllSiteT_encodedComputationalState hR label,
    allSiteT_logicalComputationalState]
  rw [map_smul]
  rfl
end QEC.Distillation.Triorthogonal.BinaryRowFamily
