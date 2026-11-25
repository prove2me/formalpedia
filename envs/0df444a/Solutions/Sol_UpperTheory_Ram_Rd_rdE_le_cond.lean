-- Prove2me | solution 1 for UpperTheory.Ram.Rd.rdE_le_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:45.514694+00:00
-- url     : https://prove2.me/submissions/2c29440a-2d1a-47fe-84dc-4cc2895478a5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_rdE_nonneg
import Theorems.Thm_UpperTheory_Ram_Rd_two_mul_rdE_le_cond

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
theorem _root_.solution : H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  linarith [two_mul_rdE_le_cond H, rdE_nonneg H]
end UpperTheory.Ram.Rd
