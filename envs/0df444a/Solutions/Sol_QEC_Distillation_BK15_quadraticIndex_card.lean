-- Prove2me | solution 1 for QEC.Distillation.BK15.quadraticIndex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T00:53:59.554852+00:00
-- url     : https://prove2.me/submissions/a9a307b9-35d1-496b-b994-cbada3f5aaf8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Fintype.card QuadraticIndex = 6 := by
  decide +kernel
end QEC.Distillation.BK15
