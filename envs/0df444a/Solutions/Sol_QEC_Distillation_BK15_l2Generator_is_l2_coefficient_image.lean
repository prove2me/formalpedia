-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Generator_is_l2_coefficient_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:49.494724+00:00
-- url     : https://prove2.me/submissions/0d199a10-47df-4308-a71a-b9da397bcfe4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ g : Sum (Fin 4) QuadraticIndex,
      l2CoefficientMap (Pi.single g 1) = l2Generator g := by
  decide +kernel
end QEC.Distillation.BK15
