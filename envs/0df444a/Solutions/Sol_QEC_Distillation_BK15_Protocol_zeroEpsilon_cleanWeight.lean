-- Prove2me | solution 1 for QEC.Distillation.BK15.Protocol.zeroEpsilon_cleanWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T02:08:24.902314+00:00
-- url     : https://prove2.me/submissions/b05bdb94-c811-49e6-836a-eb53db55bfef

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.Protocol
theorem _root_.solution : zeroEpsilon.cleanWeight = 1 := by
  norm_num [zeroEpsilon, BK15Epsilon.cleanWeight]
end QEC.Distillation.BK15.Protocol
