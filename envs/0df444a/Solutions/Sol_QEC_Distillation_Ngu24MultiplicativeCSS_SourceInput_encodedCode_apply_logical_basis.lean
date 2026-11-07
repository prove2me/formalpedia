-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.encodedCode_apply_logical_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:37.245048+00:00
-- url     : https://prove2.me/submissions/1c07570c-f083-4487-b2ec-fd52cea83dc9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_encodingLinearMap_apply_logical_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
theorem _root_.solution (data : SourceInput F I Logical)
    (u : Word F Logical) :
    data.encodedCode.encode (registerBasisKet u) = data.shortenedCosetKet u := by
  exact data.encodingLinearMap_apply_logical_basis u
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
