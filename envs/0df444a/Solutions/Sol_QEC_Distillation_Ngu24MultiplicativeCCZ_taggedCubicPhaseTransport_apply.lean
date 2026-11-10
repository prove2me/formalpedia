-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:32:13.961846+00:00
-- url     : https://prove2.me/submissions/0e073f1b-0c25-4966-b0e2-8e0204ce109c

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution (f : F →ₗ[ZMod 2] ZMod 2) (sites : Finset J)
    (psi : TaggedThreeCopyRegister F J) (label : TaggedThreeCopyRegisterLabel F J) :
    taggedCubicPhaseTransport f sites psi label =
      taggedCubicPhaseAmplitude f sites label * psi label := rfl
end QEC.Distillation.Ngu24MultiplicativeCCZ
