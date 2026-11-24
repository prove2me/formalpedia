-- Prove2me | solution 1 for ValueAwareRR.fourPermutation_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:05:01.075851+00:00
-- url     : https://prove2.me/submissions/f33737f0-45c1-45f5-aaa2-dffc6f214746

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  decide
end ValueAwareRR
