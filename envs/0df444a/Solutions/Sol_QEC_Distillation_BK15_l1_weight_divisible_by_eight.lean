-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_weight_divisible_by_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:03.147047+00:00
-- url     : https://prove2.me/submissions/36648870-690d-4e1b-ae60-e429a2d5e2b1

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ a : Fin 4 → Bit, HammingWeight (l1CoefficientMap a) % 8 = 0 := by
  decide +kernel
end QEC.Distillation.BK15
