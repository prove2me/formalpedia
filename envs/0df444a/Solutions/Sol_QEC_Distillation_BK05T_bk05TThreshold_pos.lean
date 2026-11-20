-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:42:36.483979+00:00
-- url     : https://prove2.me/submissions/222739e9-3da7-4576-b161-2161dc7cfc28

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
private theorem sqrt_three_sevenths_sq :
    Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 := by
  exact Real.sq_sqrt (by norm_num)
end BK05T
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution : 0 < bk05TThreshold := by
  have hsqrt_nonneg : 0 <= Real.sqrt (3 / 7 : Real) := Real.sqrt_nonneg _
  have hsqrt_lt_one : Real.sqrt (3 / 7 : Real) < 1 := by
    nlinarith [sqrt_three_sevenths_sq]
  unfold bk05TThreshold
  linarith
end QEC.Distillation.BK05T
