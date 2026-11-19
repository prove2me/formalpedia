-- Prove2me | solution 1 for QEC.Distillation.BK15.allOnes_not_mem_L2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:03:15.495203+00:00
-- url     : https://prove2.me/submissions/a9abff63-22f6-4f5a-87b1-0ba6d0bfb4a4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_allOnes_not_l2_coefficient_image

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : allOnes ∉ L2.carrier := by
  rintro ⟨b, hb⟩
  exact allOnes_not_l2_coefficient_image b hb
end QEC.Distillation.BK15
