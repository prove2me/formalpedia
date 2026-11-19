-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.FStar_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:10.197877+00:00
-- url     : https://prove2.me/submissions/50874770-3208-4ff0-98ea-24b5aaf350f6

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_epsilonStar_pos
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
private theorem one_sub_epsilonStar_pos : 0 < 1 - epsilonStar := by
  linarith [epsilonStar_pos, epsilonStar_lt_half]
namespace BK15SemanticSchedule
end BK15SemanticSchedule
end Threshold
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution : 0 < FStar := by
  unfold FStar
  exact Real.sqrt_pos.mpr one_sub_epsilonStar_pos
end QEC.Distillation.BK15.Threshold
