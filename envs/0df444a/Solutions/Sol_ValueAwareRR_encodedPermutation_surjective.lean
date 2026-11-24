-- Prove2me | solution 1 for ValueAwareRR.encodedPermutation_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:17:09.371153+00:00
-- url     : https://prove2.me/submissions/320fdfb3-2463-4559-b03a-a2b2afde0adc

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_encodedPermutation_bijective

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Surjective encodedPermutation :=
  encodedPermutation_bijective.surjective
end ValueAwareRR
