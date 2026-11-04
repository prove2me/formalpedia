-- Prove2me | solution 1 for ThreeSum.WeightedModuli.weighted_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:45.330353+00:00
-- url     : https://prove2.me/submissions/7e517253-f197-47de-ae47-a667dc5100c4

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Theorems.Thm_ThreeSum_WeightedModuli_weighted_count_add

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution {ι : Type*} (T : Finset ι) (difference : ι → ℤ)
    (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) (q : ℕ) :
    weightedFalseCount T difference (Auxiliary.moduli C) q =
      C.card * modCount T difference q -
        (∑ p ∈ C, modCount T difference (joint q p)) := by
  have h := weighted_count_add T difference C hC q
  omega
end ThreeSum.WeightedModuli
