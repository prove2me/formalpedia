-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_dual_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:28.205204+00:00
-- url     : https://prove2.me/submissions/eb287dbf-3815-4098-a4eb-8a8669c14ed5

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2_dimension
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Dimension L2.dual = 5 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l2_dimension]
  decide +kernel
end QEC.Distillation.BK15
