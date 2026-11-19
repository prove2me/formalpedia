-- Prove2me | solution 1 for QEC.Distillation.BK15.allOnes_not_mem_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:46.258455+00:00
-- url     : https://prove2.me/submissions/90a7caf9-2da5-42c6-a194-0e205b14b169

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_allOnes_not_l1_coefficient_image

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : allOnes ∉ L1.carrier := by
  rintro ⟨a, ha⟩
  exact allOnes_not_l1_coefficient_image a ha
end QEC.Distillation.BK15
