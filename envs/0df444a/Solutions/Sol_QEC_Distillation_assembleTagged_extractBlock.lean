-- Prove2me | solution 1 for QEC.Distillation.assembleTagged_extractBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:13.06602+00:00
-- url     : https://prove2.me/submissions/f66e85b2-ebaf-43a1-b7dd-0207824289b9

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]
omit [Field F] [Fintype F]
namespace QEC.Distillation
theorem _root_.solution (label : TaggedThreeCopyRegisterLabel F ι) :
    assembleTagged (extractBlock label) = label := by
  funext coordinate
  rcases coordinate with ⟨tag, site⟩
  rfl
end QEC.Distillation
