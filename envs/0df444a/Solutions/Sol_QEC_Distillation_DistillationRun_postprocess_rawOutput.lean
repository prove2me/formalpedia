-- Prove2me | solution 1 for QEC.Distillation.DistillationRun.postprocess_rawOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:23.744763+00:00
-- url     : https://prove2.me/submissions/532b44fb-c2df-453a-93eb-26a0baca3c21

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol

set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open QEC.Distillation.DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
namespace QEC.Distillation.DistillationRun
theorem _root_.solution {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output') :
    (run.postprocess channel).rawOutput =
      channel.mapDensity run.rawOutput := by
  rfl
end QEC.Distillation.DistillationRun
