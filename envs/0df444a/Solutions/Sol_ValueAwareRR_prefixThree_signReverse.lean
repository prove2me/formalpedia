-- Prove2me | solution 1 for ValueAwareRR.prefixThree_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:57:23.818261+00:00
-- url     : https://prove2.me/submissions/d8c0dd65-6374-4ffe-a385-dad1f7ca0e67

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_orderedResidual_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    prefixThree m (signReverse o) = -prefixThree m o := by
  simp only [prefixThree, orderedResidual_signReverse]
  ring
end ValueAwareRR
