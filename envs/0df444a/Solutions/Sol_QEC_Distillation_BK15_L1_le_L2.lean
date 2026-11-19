-- Prove2me | solution 1 for QEC.Distillation.BK15.L1_le_L2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:26.96847+00:00
-- url     : https://prove2.me/submissions/9143ca72-f9a4-4bc9-b284-cad05099546a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1_coefficient_has_l2_presentation

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : L1.carrier ≤ L2.carrier := by
  rintro w ⟨a, rfl⟩
  rcases l1_coefficient_has_l2_presentation a with ⟨b, hb⟩
  exact ⟨b, hb⟩
end QEC.Distillation.BK15
