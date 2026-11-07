-- Prove2me | solution 1 for QEC.Distillation.mem_coordinateSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:19:49.58299+00:00
-- url     : https://prove2.me/submissions/48465fe0-7657-4e82-a72e-e7a479d86e0e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]
namespace QEC.Distillation
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    {coordinate : TaggedThreeCopyCoordinate ι} {site : ι} :
    coordinate ∈ coordinateSupport site ↔ coordinate.2 = site := by
  simp [coordinateSupport]
end QEC.Distillation
