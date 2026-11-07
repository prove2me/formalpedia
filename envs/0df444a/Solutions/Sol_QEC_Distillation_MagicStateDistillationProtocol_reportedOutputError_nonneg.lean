-- Prove2me | solution 1 for QEC.Distillation.MagicStateDistillationProtocol.reportedOutputError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:12.509422+00:00
-- url     : https://prove2.me/submissions/7394fdba-451a-4431-940e-b58c865b93c2

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol

set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
open QEC.Distillation.MagicStateDistillationProtocol
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
namespace QEC.Distillation.MagicStateDistillationProtocol
theorem _root_.solution
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    0 ≤ protocol.reportedOutputError :=
  protocol.outputError_nonneg _ _
end QEC.Distillation.MagicStateDistillationProtocol
