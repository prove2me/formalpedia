-- Prove2me | solution 1 for ValueAwareRR.encodedPermutation_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:55.162168+00:00
-- url     : https://prove2.me/submissions/7121884d-0fc2-45ec-a343-ea3e5486b92b

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_orderAt_injective

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Injective encodedPermutation := by
  intro o p hop
  apply orderAt_injective
  funext k
  exact congrArg (fun q : Equiv.Perm (Fin 4) => q k) hop
end ValueAwareRR
