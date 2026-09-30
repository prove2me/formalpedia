-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.EnumerationProbe.toyMaximum_le_28_yukon_122fdfd0905d
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-29T23:01:52.170431+00:00
-- url     : https://prove2.me/submissions/ab0a68b6-5ce8-416f-852f-2610247de911

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
import Definitions.Def_Yukon_d9f5b00d74e4bca418786f45
/-!
# A kernel-evaluated small analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It asks the
remote verifier to exhaust all eight-subsets of the fifteen nontrivial powers
of a primitive sixteenth root in `ZMod 17`, represented by natural residues.
The two key coordinates are the first Newton coefficient and the product
exponent modulo sixteen.  Candidates are traversed once while accumulating a
`16 × 17` histogram, so the expensive key calculation is not repeated for
every possible key.  A preceding remote smoke test established that this
histogram evaluates within the verifier budget, and a second run proved the
upper bounds 64, 44, 34, and 29, while a remote run proved that the bound 26 is
false.  This probe asks whether every fibre has size at most 28.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem _root_.solution : toyMaximum ≤ 28  := by
  decide
end EnumerationProbe
end SubmissionUpper
end ProximityPrize
