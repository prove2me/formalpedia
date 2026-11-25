-- Prove2me | solution 1 for UpperTheory.Ram.Rd.log_QS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:51.880585+00:00
-- url     : https://prove2.me/submissions/9b8fa34e-7198-4547-9634-e8bb05be882b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_one_le_QS_real
import Theorems.Thm_UpperTheory_Ram_Rd_QS_le_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Rd
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Ram.Rd
theorem _root_.solution : Real.log H.QS ≤ 2 * Real.log R.n := by
  calc Real.log H.QS ≤ Real.log ((R.n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith [one_le_QS_real H]) (QS_le_real H)
    _ = 2 * Real.log R.n := by rw [Real.log_pow]; norm_num
end UpperTheory.Ram.Rd
