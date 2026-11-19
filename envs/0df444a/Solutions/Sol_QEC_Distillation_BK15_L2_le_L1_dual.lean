-- Prove2me | solution 1 for QEC.Distillation.BK15.L2_le_L1_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:30.446061+00:00
-- url     : https://prove2.me/submissions/05aa002a-6547-458a-a43a-48d725ea9a78

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2_l1_pairing_zero

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : L2.carrier ≤ L1.dual.carrier := by
  rintro w ⟨b, rfl⟩
  refine (L1.mem_dual _).2 ?_
  rintro c ⟨a, rfl⟩
  exact l2_l1_pairing_zero b a
end QEC.Distillation.BK15
