-- Prove2me | solution 1 for UpperTheory.Ram.Rd.rdE_le_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:13.453105+00:00
-- url     : https://prove2.me/submissions/fd6327a1-f7a5-4fda-bfd4-3bfefbfcd7d6

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
theorem _root_.solution : H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := H.der.rd_le
end UpperTheory.Ram.Rd
