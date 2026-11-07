-- Prove2me | solution 1 for QEC.Distillation.DistillationRun.conditionalOutput_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:06.951203+00:00
-- url     : https://prove2.me/submissions/5d7897f4-add2-44ed-b38a-69728aaa1720

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol

set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
open QEC.Distillation.DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]
namespace QEC.Distillation.DistillationRun
theorem _root_.solution
    (run : DistillationRun Resource Input Output)
    (outcome : DistillationOutcome) :
    LinearMap.trace Complex Output (run.conditionalOutput outcome).toOperator = 1 :=
  (run.conditionalOutput outcome).trace_one
end QEC.Distillation.DistillationRun
