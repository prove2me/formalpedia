-- Prove2me | solution 1 for QEC.Distillation.DistillationRun.rawOutput_eq_outcomeMixture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:08.020699+00:00
-- url     : https://prove2.me/submissions/dbd02943-31ca-47bd-b654-43b4c7fa4c47

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
    (run : DistillationRun Resource Input Output) :
    run.rawOutput =
      outcomeMixture run.successProbability run.success_nonneg run.success_le_one
        run.acceptedOutput run.rejectedOutput :=
  run.output_decomposition
end QEC.Distillation.DistillationRun
