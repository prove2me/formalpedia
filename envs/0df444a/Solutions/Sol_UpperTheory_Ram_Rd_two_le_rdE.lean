-- Prove2me | solution 1 for UpperTheory.Ram.Rd.two_le_rdE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:04.493963+00:00
-- url     : https://prove2.me/submissions/72cc98b1-bc05-4ded-a0c1-7b991bcaa363

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_four_le_rdE

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
theorem _root_.solution : 2 ≤ H.rdE := by
  linarith [four_le_rdE H]
end UpperTheory.Ram.Rd
