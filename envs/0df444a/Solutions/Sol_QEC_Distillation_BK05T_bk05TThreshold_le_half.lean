-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TThreshold_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:01:17.34818+00:00
-- url     : https://prove2.me/submissions/7a34fcdd-86fa-47a2-9e1a-cb920e58ed71

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Theorems.Thm_QEC_Distillation_BK05T_bk05TThreshold_lt_half

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution : bk05TThreshold <= 1 / 2 :=
  bk05TThreshold_lt_half.le
end QEC.Distillation.BK05T
