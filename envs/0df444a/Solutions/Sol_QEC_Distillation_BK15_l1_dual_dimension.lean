-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_dual_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:24.999864+00:00
-- url     : https://prove2.me/submissions/9f033e93-4e4a-4aa3-8752-776db448bff8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1_dimension
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Dimension L1.dual = 11 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l1_dimension]
  decide +kernel
end QEC.Distillation.BK15
