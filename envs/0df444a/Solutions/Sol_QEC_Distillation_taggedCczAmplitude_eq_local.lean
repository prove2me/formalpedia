-- Prove2me | solution 1 for QEC.Distillation.taggedCczAmplitude_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:37.108004+00:00
-- url     : https://prove2.me/submissions/b83cca88-b898-468c-abcd-be7ecfb55a48

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
omit [Fintype F]
namespace QEC.Distillation
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label =
      cczAmplitude (label (ThreeCopyTag.first, site))
        (label (ThreeCopyTag.second, site))
        (label (ThreeCopyTag.third, site)) :=
  rfl
end QEC.Distillation
