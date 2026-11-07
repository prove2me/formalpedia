-- Prove2me | solution 1 for QEC.Distillation.extractBlock_assembleTagged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:06.086146+00:00
-- url     : https://prove2.me/submissions/faf793aa-c3db-4f45-bcfc-c85edbfc557e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]
omit [Field F] [Fintype F]
namespace QEC.Distillation
theorem _root_.solution
    (blocks : ThreeCopyTag → ComputationalBasisRegisterLabel F ι) (tag : ThreeCopyTag) :
    extractBlock (assembleTagged blocks) tag = blocks tag :=
  rfl
end QEC.Distillation
