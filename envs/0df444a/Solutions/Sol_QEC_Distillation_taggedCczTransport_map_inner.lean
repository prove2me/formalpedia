-- Prove2me | solution 1 for QEC.Distillation.taggedCczTransport_map_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:17:31.944204+00:00
-- url     : https://prove2.me/submissions/6666b3e1-3b8d-42c6-ae2b-8567bf846712

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
    (site : ι) (psi chi : TaggedThreeCopyRegister F ι) :
    inner Complex (taggedCczTransport site psi) (taggedCczTransport site chi) =
      inner Complex psi chi :=
  taggedCczDiagonalOperator_map_inner site psi chi
end QEC.Distillation
