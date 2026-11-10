-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.f256QuditEncodedCode_measurementDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:01:41.474181+00:00
-- url     : https://prove2.me/submissions/a08893b1-d522-45e5-b83f-abb1fe0d1d67

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_measurementDistance


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_a61e848631_24
namespace QEC.Distillation.Ngu24MultiplicativeCSS
theorem _root_.solution (i : ℕ) :
    QuditSubsystem.BPTMeasurementDistance
      ((f256QuditEncodedCode i).code.transport
        (FiniteAlphabet.registerUnitary F256 (f256SourceInput i).PivotComplement))
      (f256QuditDistanceBound i) :=
  f256SourceInput_measurementDistance i
end QEC.Distillation.Ngu24MultiplicativeCSS
