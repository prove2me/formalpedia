-- Prove2me | solution 1 for QEC.Distillation.BK15.l2CoefficientMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:59:51.257664+00:00
-- url     : https://prove2.me/submissions/2ac2149a-7265-44c6-94b4-0eeece203fdb

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (a : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap a ∈ L2.carrier :=
  ⟨a, rfl⟩
end QEC.Distillation.BK15
