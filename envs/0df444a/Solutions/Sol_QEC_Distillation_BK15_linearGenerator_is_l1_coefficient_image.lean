-- Prove2me | solution 1 for QEC.Distillation.BK15.linearGenerator_is_l1_coefficient_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:11.989757+00:00
-- url     : https://prove2.me/submissions/6e295c6e-1573-4412-8d3a-94aadd3ef80b

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ j : Fin 4, l1CoefficientMap (Pi.single j 1) = linearGenerator j := by
  decide +kernel
end QEC.Distillation.BK15
