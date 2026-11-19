-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Generator_mem_L2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:04:52.004193+00:00
-- url     : https://prove2.me/submissions/8d56885d-1d9f-43d1-aead-a462a4867038

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2Generator_is_l2_coefficient_image

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (g : Sum (Fin 4) QuadraticIndex) :
    l2Generator g ∈ L2.carrier :=
  ⟨Pi.single g 1, l2Generator_is_l2_coefficient_image g⟩
end QEC.Distillation.BK15
