-- Prove2me | solution 1 for QEC.Distillation.BK15.allOnes_not_l1_coefficient_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:01:02.029147+00:00
-- url     : https://prove2.me/submissions/87abc436-08e9-405c-bb07-17bec8aa9fca

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ a : Fin 4 → Bit, l1CoefficientMap a ≠ allOnes := by
  decide +kernel
end QEC.Distillation.BK15
