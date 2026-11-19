-- Prove2me | solution 1 for QEC.Distillation.BK15.Protocol.oneSiteWord_l2Syndrome_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T02:08:21.766199+00:00
-- url     : https://prove2.me/submissions/6828965e-572e-403a-ab44-46bbeb70a5c9

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
theorem _root_.solution (site : Fin 15) :
    l2Syndrome (oneSiteWord site) ≠ 0 := by
  decide +kernel +revert
end QEC.Distillation.BK15.Protocol
