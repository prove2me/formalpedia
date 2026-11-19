-- Prove2me | solution 1 for QEC.Distillation.BK15.allOnes_not_l2_coefficient_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:00:57.226483+00:00
-- url     : https://prove2.me/submissions/ad3d4770-dbe1-46be-9754-8de586e2c83e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit, l2CoefficientMap b ≠ allOnes := by
  decide +kernel
end QEC.Distillation.BK15
