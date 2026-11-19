-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_coefficient_has_l2_presentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:00:45.30282+00:00
-- url     : https://prove2.me/submissions/abe1a0ad-24f0-4494-8f69-91c2cdc59bc6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ a : Fin 4 → Bit,
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit,
        l2CoefficientMap b = l1CoefficientMap a := by
  decide +kernel
end QEC.Distillation.BK15
