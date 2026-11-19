-- Prove2me | solution 1 for QEC.Distillation.BK15.l1CoefficientMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:59:48.000238+00:00
-- url     : https://prove2.me/submissions/394b0d94-efbe-47dd-9c49-a826b20ed71c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (a : Fin 4 → Bit) :
    l1CoefficientMap a ∈ L1.carrier :=
  ⟨a, rfl⟩
end QEC.Distillation.BK15
