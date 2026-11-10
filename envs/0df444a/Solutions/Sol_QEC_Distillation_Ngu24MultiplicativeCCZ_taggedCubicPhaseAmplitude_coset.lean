-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseAmplitude_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:32:16.570888+00:00
-- url     : https://prove2.me/submissions/f95a3cda-51b5-4eee-87b6-d7178ba0caad

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
variable [Fintype I] [Fintype Logical] [CharP F 2]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_bfada1b37a_179
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    taggedCubicPhaseAmplitude f Finset.univ (taggedShortenedCosetLabel data label h) =
      taggedCubicPhaseAmplitude f Finset.univ label := by
  unfold taggedCubicPhaseAmplitude
  congr 2
  exact taggedShortenedCosetLabel_cubic_identity data label h
end QEC.Distillation.Ngu24MultiplicativeCCZ
