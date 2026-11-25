-- Prove2me | solution 1 for UpperTheory.Ram.Rd.QS_le_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:10.440434+00:00
-- url     : https://prove2.me/submissions/e915ea23-accb-4609-bb8f-f849586b18db

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN

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
theorem _root_.solution : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
end UpperTheory.Ram.Rd
