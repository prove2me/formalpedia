-- Prove2me | solution 1 for QEC.Distillation.BK15.l2DualCoefficientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:53:27.618938+00:00
-- url     : https://prove2.me/submissions/247b2d3a-04dd-457d-8b79-360c845d37aa

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Function.Injective l2DualCoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
