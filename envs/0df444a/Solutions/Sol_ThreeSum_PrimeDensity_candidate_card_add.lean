-- Prove2me | solution 1 for ThreeSum.PrimeDensity.candidate_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:56.663731+00:00
-- url     : https://prove2.me/submissions/f974809b-4b53-43ce-ab54-94e5526f5711

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution (y : ℕ) :
    (candidates y).card + Nat.primeCounting y = Nat.primeCounting (4 * y) := by
  have hsub : Nat.primesLE y ⊆ Nat.primesLE (4 * y) := Nat.primesLE_mono (by omega)
  simpa only [candidates, Nat.primesLE_card_eq_primeCounting] using card_sdiff_add_card_eq_card hsub
end ThreeSum.PrimeDensity
