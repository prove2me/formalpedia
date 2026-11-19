-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_pointwiseProduct_weight_divisible_by_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:27.299011+00:00
-- url     : https://prove2.me/submissions/92dbaa3a-a72c-483f-bcf9-8f47dd81b6f4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ (a b : Fin 4 → Bit),
      HammingWeight (pointwiseProduct (l1CoefficientMap a) (l1CoefficientMap b)) % 4 = 0 := by
  decide +kernel
end QEC.Distillation.BK15
