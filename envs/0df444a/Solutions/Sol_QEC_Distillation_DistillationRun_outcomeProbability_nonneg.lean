-- Prove2me | solution 1 for QEC.Distillation.DistillationRun.outcomeProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:58.307204+00:00
-- url     : https://prove2.me/submissions/4b35663f-db29-4ff3-9095-e62a1da5d234

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
    0 ≤ run.outcomeProbability outcome :=
  outcomeWeight_nonneg run.success_nonneg run.success_le_one outcome
end QEC.Distillation.DistillationRun
