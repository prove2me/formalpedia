-- Prove2me | solution 1 for QEC.Distillation.BK15.linearGenerator_mem_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:03:36.826207+00:00
-- url     : https://prove2.me/submissions/d585156e-bfb6-4475-bf22-1a4870f64dce

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_linearGenerator_is_l1_coefficient_image

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (j : Fin 4) : linearGenerator j ∈ L1.carrier :=
  ⟨Pi.single j 1, linearGenerator_is_l1_coefficient_image j⟩
end QEC.Distillation.BK15
