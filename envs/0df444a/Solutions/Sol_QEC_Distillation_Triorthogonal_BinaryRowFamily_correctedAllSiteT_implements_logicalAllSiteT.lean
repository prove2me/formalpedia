-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:47:00.713322+00:00
-- url     : https://prove2.me/submissions/9f065a2c-1347-421f-bf27-18c146d230ba

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_intertwines_encoding

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
universe v
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    (R.encodedCode hR).ImplementsLogicalGate R.correctedAllSiteT
      (allSiteT (Index := LogicalRow)) := by
  intro psi
  change R.correctedAllSiteT
      (R.encoding hR psi : Qubit.QubitRegister PhysicalCol) =
    (R.encoding hR ((allSiteT (Index := LogicalRow)) psi) :
      Qubit.QubitRegister PhysicalCol)
  exact R.correctedAllSiteT_intertwines_encoding hR psi
end QEC.Distillation.Triorthogonal.BinaryRowFamily
