-- Prove2me | solution 1 for UpperTheory.Ram.Rd.two_mul_rdE_le_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:51.956846+00:00
-- url     : https://prove2.me/submissions/460fb292-dbc8-4522-9458-f4488f8f3846

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_rdE_le_QS
import Theorems.Thm_UpperTheory_Ram_Rd_sqrt_qd_le

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
theorem _root_.solution : 2 * H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have h1 := rdE_le_QS H
  have h2 := sqrt_qd_le H
  have h3 : (0 : ℝ) ≤ H.QS := by positivity
  calc 2 * H.rdE ≤ (H.QS : ℝ) * Real.sqrt ((H.q : ℝ) * H.d) := by linarith
    _ ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) := mul_le_mul_of_nonneg_left h2 h3
    _ = (H.QS : ℝ) * H.q * H.d := by ring
end UpperTheory.Ram.Rd
