-- Prove2me | solution 1 for QEC.Distillation.BK15.l1DualCoefficientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:52:48.201939+00:00
-- url     : https://prove2.me/submissions/e694b5ef-7b24-4c41-b6a0-b8d1cc28d641

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Function.Injective l1DualCoefficientMap := by
  -- A linear map is injective iff its kernel is zero; enumerate inputs, not pairs.
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
