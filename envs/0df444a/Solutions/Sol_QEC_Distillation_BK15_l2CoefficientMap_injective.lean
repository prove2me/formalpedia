-- Prove2me | solution 1 for QEC.Distillation.BK15.l2CoefficientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:53:55.79196+00:00
-- url     : https://prove2.me/submissions/81c4ce93-71af-4ef3-b631-3a777274dd15

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Function.Injective l2CoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
