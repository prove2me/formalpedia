-- Prove2me | solution 1 for PermanentRollout.sliceRank_lt_blockVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/102958ce-525f-4486-a458-80c70afb599f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hm : 8 ≤ blockVariables n d) :
    sliceRank n d < blockVariables n d := by
  unfold sliceRank
  exact Nat.div_lt_self (by omega) (by omega)
end PermanentRollout
