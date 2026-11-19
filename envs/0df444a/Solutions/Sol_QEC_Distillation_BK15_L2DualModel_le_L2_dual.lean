-- Prove2me | solution 1 for QEC.Distillation.BK15.L2DualModel_le_L2_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:03:18.708324+00:00
-- url     : https://prove2.me/submissions/c21088df-52da-4c03-9495-9896d5ce994c

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualModel_l2_pairing_zero

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : L2DualModel.carrier ≤ L2.dual.carrier := by
  rintro w ⟨ac, rfl⟩
  refine (L2.mem_dual _).2 ?_
  rintro c ⟨b, rfl⟩
  exact l2DualModel_l2_pairing_zero ac b
end QEC.Distillation.BK15
