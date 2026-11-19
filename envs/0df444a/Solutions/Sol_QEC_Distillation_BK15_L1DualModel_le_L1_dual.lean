-- Prove2me | solution 1 for QEC.Distillation.BK15.L1DualModel_le_L1_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:04:11.870098+00:00
-- url     : https://prove2.me/submissions/5ec57eea-dd69-4330-ae4f-64c4a1ad9702

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1DualModel_l1_pairing_zero

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : L1DualModel.carrier ≤ L1.dual.carrier := by
  rintro w ⟨bc, rfl⟩
  refine (L1.mem_dual _).2 ?_
  rintro c ⟨a, rfl⟩
  exact l1DualModel_l1_pairing_zero bc a
end QEC.Distillation.BK15
