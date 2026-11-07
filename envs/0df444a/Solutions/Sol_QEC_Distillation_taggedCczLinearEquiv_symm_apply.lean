-- Prove2me | solution 1 for QEC.Distillation.taggedCczLinearEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:23:12.475397+00:00
-- url     : https://prove2.me/submissions/4855e6c6-9fc7-48fd-a980-84d0ea9b0eea

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
namespace QEC.Distillation
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    (site : ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    (taggedCczLinearEquiv (F := F) site).symm psi label =
      taggedCczAmplitude site label * psi label :=
  rfl
end QEC.Distillation
