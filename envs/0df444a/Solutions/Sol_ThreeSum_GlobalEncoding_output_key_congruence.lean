-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.output_key_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:29:45.95273+00:00
-- url     : https://prove2.me/submissions/7938ae9f-2202-4de6-b0c0-6f3ee218085e

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_globalKey_outputOfChoices
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h J : ℕ} {a b : ℤ}
    {xs : List (RetainedChoice h)} (hxs : xs ∈ representations h J a b) :
    globalModulus h J ∣ (b - a) -
      globalKey (outputOfChoices xs ((mem_representations h J a b xs).mp hxs).1) := by
  obtain ⟨hlen, ha, hb⟩ := (mem_representations h J a b xs).mp hxs
  rw [globalKey_outputOfChoices]
  have he : (b - a) -
      (Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs) =
      (b - Radix.positionalHash (localPrime h) rawRight xs) -
        (a - Radix.positionalHash (localPrime h) rawLeft xs) := by ring
  rw [he]
  exact dvd_sub hb ha
end ThreeSum.GlobalEncoding
