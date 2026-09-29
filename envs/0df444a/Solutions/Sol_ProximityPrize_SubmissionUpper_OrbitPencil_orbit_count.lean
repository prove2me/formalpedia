-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.OrbitPencil.orbit_count
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:27:59.979756+00:00
-- url     : https://prove2.me/submissions/70bb0b27-428c-445f-baf9-9556ce2617a3

import Mathlib
import Init
/-!
# A rational pencil on the 512-by-512 NTT grid

The size-`2^18` NTT domain is partitioned into 512 fibres by `x ↦ x^512`.
We use 272 whole fibres together with a fixed 511-point core.  Prescribing 14
top coefficients and the product of the selected fibre labels leaves more than
`2^59` choices while forcing pairwise differences to have the two roots needed
to fit under the row-degree budget.
-/

namespace ProximityPrize.SubmissionUpper.OrbitPencil

open Polynomial
                                   
                             
open scoped NNReal BigOperators















































































set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem _root_.solution :
    ((2 ^ 31 - 2 ^ 24 + 1)^14 * 512) * 2^59 < Nat.choose 511 272 := (by
  rw [Nat.choose_eq_fast_choose]
  decide
)
end OrbitPencil
end SubmissionUpper
end ProximityPrize
