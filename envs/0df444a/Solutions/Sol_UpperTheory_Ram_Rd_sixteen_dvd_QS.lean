-- Prove2me | solution 1 for UpperTheory.Ram.Rd.sixteen_dvd_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:43:17.941601+00:00
-- url     : https://prove2.me/submissions/6809179d-ab06-434a-827f-7eedba0f4408

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
theorem _root_.solution : 16 ∣ H.QS := by
  have he := H.two_le_e
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ (R.e + 2) := Nat.pow_dvd_pow 2 (by omega)
    _ ∣ H.QS := H.tower_dvd
end UpperTheory.Ram.Rd
