-- Prove2me | solution 1 for QEC.Distillation.MagicStateDistillationProtocol.successfulOutputError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:58:09.839569+00:00
-- url     : https://prove2.me/submissions/f21be279-6bc4-4ef8-aa5b-405a3f62ae94

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
    0 ≤ protocol.successfulOutputError :=
  protocol.outputError_nonneg _ _
end QEC.Distillation.MagicStateDistillationProtocol
