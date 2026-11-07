-- Prove2me | solution 1 for QEC.Distillation.MagicStateDistillationProtocol.inputModel_permits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:16.871786+00:00
-- url     : https://prove2.me/submissions/263fbfb5-1bbb-4b6c-91e4-f07d41bd65f6

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
    protocol.inputErrorModel.Permits protocol.run.noisyInput :=
  protocol.inputPermitted
end QEC.Distillation.MagicStateDistillationProtocol
