-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_l2Dual_pointwiseProduct_weight_divisible_by_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:30.461412+00:00
-- url     : https://prove2.me/submissions/8c3b4873-5f8a-4ec6-b388-aba9e82f0a74

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ (a : Fin 4 → Bit) (ac : (Fin 4 → Bit) × Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l2DualCoefficientMap ac)) % 4 = 0 := by
  decide +kernel
end QEC.Distillation.BK15
