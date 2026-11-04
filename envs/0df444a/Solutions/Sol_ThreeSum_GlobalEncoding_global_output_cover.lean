-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.global_output_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:40.818589+00:00
-- url     : https://prove2.me/submissions/36064766-aa73-4504-a700-636d3c7bbe55

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_representations_nonempty
import Theorems.Thm_ThreeSum_GlobalEncoding_globalKey_outputOfChoices
import Theorems.Thm_ThreeSum_GlobalEncoding_output_key_congruence
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
import Theorems.Thm_ThreeSum_Radix_representations_nonempty


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    ∃ xs ∈ representations h J a b, ∃ q : GlobalOutput h J,
      globalKey q = Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ (b - a) - globalKey q := by
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J a b
  let hlen := ((mem_representations h J a b xs).mp hxs).1
  exact ⟨xs, hxs, outputOfChoices xs hlen, globalKey_outputOfChoices xs hlen,
    output_key_congruence hxs⟩
end ThreeSum.GlobalEncoding
