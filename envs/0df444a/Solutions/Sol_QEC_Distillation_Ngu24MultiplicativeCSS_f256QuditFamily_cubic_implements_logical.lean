-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditFamily_cubic_implements_logical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:01:50.392202+00:00
-- url     : https://prove2.me/submissions/e5a6073f-36b4-44e4-bfb8-47d5932f2a7c

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_implements_logical


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_111
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_112
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ)
    (f : F256 →ₗ[ZMod 2] ZMod 2) :
    (taggedEncodedCode (f256SourceInput i)).ImplementsLogicalGate
      (taggedCubicPhysicalTransport f)
      (taggedCubicPhaseTransport f Finset.univ) :=
  taggedCubicPhysicalTransport_implements_logical (f256SourceInput i) f
end QEC.Distillation.Ngu24MultiplicativeCSS
